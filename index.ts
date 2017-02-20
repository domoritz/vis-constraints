#! /usr/local/bin/node

import {exec} from "child_process";
import * as stream from "stream";
import * as fs from "fs";
import {softConstraints} from "./softConstraints";
import {hardConstraints, assert, eq, not, or} from "./hardConstraints";

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
  PointMark BarMark LineMark AreaMark TextMark TickMark RuleMark RectMark
)))

(declare-datatypes () ((Channel 
  X Y Color Size Shape Text Detail
)))

(declare-datatypes () ((FieldType 
  Quantitative Ordinal Nominal
)))

(declare-datatypes () ((AggFunc 
  None Count Sum Mean Median Min Max
)))

(declare-datatypes () ((Scale 
  (mk-scale (zero bool))
)))

(declare-datatypes () ((Encoding
  (mk-enc (channel Channel) (field Field) (type FieldType) (binned Bool) (agg AggFunc) (scale Scale))
)))
`;

const countField = `
(declare-const countField Field)
(assert (= (name countField) "*"))
(assert (= (type countField) Integer))
`

const markDeclaration = `
(declare-const mark Marktype)
`

const solve = `
; get output
(check-sat)
; (get-model)
`;

function buildProgram(fields: {name: string, type: string}[], query) {
  let program = "";
  
  program += types;
  program += markDeclaration;
  program += countField;

  // add fields
  fields.forEach(f => {
    const name = f.name + "Field";
    program += `
    (declare-const ${name} Field)
    (assert (= (name ${name}) "${f.name}"))
    (assert (= (type ${name}) ${f.type}))
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
        program += assert(eq(`(name (field ${enc}))`, `"${e.field}"`));
      }
      if (e.channel) {
        program += assert(eq(`(channel ${enc})`, `${e.channel}`));
      }
      if (e.binned !== undefined) {
        if (e.binned) {
          program += assert(`(binned ${enc})`);
        } else {
          program += assert(not(`(binned ${enc})`));
        }
      }

      // encoding has to use one of the fields
      const encodingField = fields.map(f =>
        eq(`(field ${enc})`, `${f.name}Field`)
      );
      encodingField.push(eq(`(field ${enc})`, "countField"));
      program += assert(or(...encodingField));

      encs.push(enc);
    });
  }

  // add constraints

  if (encs.length === 0) {
    // we need at least one channel
    program += assert("false");
  } else {
    program += hardConstraints(encs);
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
    { field: "str1"},
    { field: "num1", channel: "Color" },
    { field: "*"}
  ]
}

const program = buildProgram(fields, query);

if (process.argv[2] === "-o") {
  // output program instead of passing it to z3
  console.log(program);
} else {
  console.time("z3");

  // execute in z3
  const child = exec("z3 /dev/fd/0", function (err, stdout, stderr) {
    if (err) {
      console.error(err);
    }
    if (stderr) {
      console.error(stderr);
    }

    console.timeEnd("z3");

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
