#! /usr/local/bin/node

import {exec} from "child_process";
import * as stream from "stream";
import * as fs from "fs";
import {softConstraints} from "./softConstraints";

const types = `
; data related types

(declare-datatypes () ((RawType 
  String Number Integer Date
)))

(declare-datatypes () ((Field 
  (mk-field (name String) (type RawType))
)))

; encoding related types

(declare-datatypes () ((Marktype 
  PointMark BarMark LineMark AreaMark SymbolMark TextMark TickMark
)))

(declare-datatypes () ((Channel 
  X Y Color Size Shape Text Detail
)))

(declare-datatypes () ((FieldType 
  Quantitative Ordinal Nominal
)))

(declare-datatypes () ((AggFunc 
  None Count Mean Median Min Max
)))

(declare-datatypes () ((ScaleType 
  LinearScale SequentialScale OrdinalScale PointScale BandScale
)))

(declare-datatypes () ((Scale 
  (mk-scale (type ScaleType) (zero bool))
)))

(declare-datatypes () ((Encoding
  (mk-enc (channel Channel) (field Field) (type FieldType) (binned Bool) (agg AggFunc) (scale Scale))
)))
`;

const declaration = `
(declare-const mark Marktype)
`

const solve = `
; get output
(check-sat)
; (get-model)
`;

function assert(s: string) {
  return `(assert ${s})\n\n`;
}

function implies(a: string, b: string) {
  return `(=> ${a} ${b})\n`;
}

function and(...exprs: string[]) {
  return `(and
    ${exprs.join("\n")}
  )`;
}

function or(...exprs: string[]) {
  return `(or
    ${exprs.join("\n")}
  )`;
}

function eq(a: string, b: string) {
  return `(= ${a} ${b})`;
}

function not(s) {
  return `(not ${s})`;
}

function buildProgram(fields: {name: string, type: string}[], query) {
  let program = "";
  
  program += types;
  program += declaration;

  // add fields
  fields.forEach(f => {
    program += `
    (declare-const ${f.name} Field)
    (assert (= (name ${f.name}) "${f.name}"))
    (assert (= (type ${f.name}) ${f.type}))
    `;
  });
  
  // add mark type constraint
  if (query.mark) {
    program += assert(eq("mark", `${query.mark}Mark`));
  }

  // add encodings
  const encs = [];
  if (query.encoding) {
    query.encoding.forEach((e, i) => {
      const enc = `e${i}`;
      program += `(declare-const ${enc} Encoding)`;
      if (e.field) {
        program += assert(eq(`(field ${enc})`, `${e.field}`));
      }
      if (e.channel) {
        program += assert(eq(`(channel ${enc})`, `${e.channel}`));
      }
      encs.push(enc);
    });
  }

  // add constraints

  if (encs.length === 0) {
    // we need at least one channel
    program += assert("false");
  } else {
    const barOrTick = or(eq("mark", "BarMark"), eq("mark", "TickMark"));

    // cannot use the same channel twice
    const channels = encs.map(e => `(channel ${e})`).join(" ");
    program += assert(`(distinct ${channels})`);

    // bar mark requires scale to start at zero
    const zeroScale = encs.map(e => implies(
      and(
        or(eq(`(channel ${e})`, "X"), eq(`(channel ${e})`, "Y")),
        eq(`(type ${e})`, "Quantitative")
      ),
      `(zero (scale ${e}))`
    ));

    program += assert(implies(eq("mark", "BarMark"), and(...zeroScale)))

    // bar and tick should not use size
    const channelsSize = encs.map(e => eq(`(channel ${e})`, "Size"));
    program += assert(implies(barOrTick, not(or(...channelsSize))));

    // bar and tick mark needs ordinal, nominal, or binned quantitative on X or Y
    const channelsCat = encs.map(e =>
      and(
        or(eq(`(channel ${e})`, "X"), eq(`(channel ${e})`, "Y")),
        or(
          eq(`(type ${e})`, "Ordinal"),
          eq(`(type ${e})`, "Nominal"),
          and(
            eq(`(type ${e})`, "Quantitative")),
            `(binned ${e})`
          )
        )
      );

    program += assert(implies(barOrTick, or(...channelsCat)));

    // text channel can only be used with text mark, and text channel is required
    const channelsText = encs.map(e => eq(`(channel ${e})`, "Text"));
    program += assert(eq(eq("mark", "TextMark"), or(...channelsText)));

    // shape requires symbol mark
    const channelsShape = encs.map(e => eq(`(channel ${e})`, "Shape"));
    program += assert(eq(eq("mark", "SymbolMark"), or(...channelsShape)));

  }

  // FIXME: greg
  // const [defs, minimizeStmt] = softConstraints(fields, query)

  // program += defs;
  // program += minimizeStmt;

  program += solve;

  program += `
  (echo "Marktype:")
  (get-value (mark))
  `
  program += `
  (echo "Encodings:")
  ${encs.map(e => `(get-value (${e}))`).join("\n")}
  `;

  return program;
}

const fields = [{
  name: "int1",
  type: "Integer"
}, {
  name: "int2",
  type: "Integer"
}, {
  name: "num1",
  type: "Number"
}, {
  name: "num2",
  type: "Number"
}, {
  name: "str1",
  type: "String"
}, {
  name: "str2",
  type: "String"
}];

const query = {
  mark: "Bar",
  encoding: [
    { field: "str1" },
    { field: "num1", channel: "Color" },
    { field: "int1" }
  ]
}

const program = buildProgram(fields, query);

if (process.argv[2] === "-o") {
  // output program instead of passing it to z3
  console.log(program);
} else {
  // execute in z3
  const child = exec("z3 /dev/fd/0", function (err, stdout, stderr) {
    if (err) {
      console.error(err);
    }
    if (stderr) {
      console.error(stderr);
    }
    // TODO: parse
    console.log(stdout);
  });

  if (process.argv[2] === "-d") {
    fs.writeFile("out.z3", program, () => {});
  }
  
  const stdinStream = new stream.Readable();
  
  stdinStream.push(program);  // Add data to the internal queue for users of the stream to consume
  stdinStream.push(null);   // Signals the end of the stream (EOF)
  stdinStream.pipe(child.stdin);
}
