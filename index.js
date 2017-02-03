#! /usr/local/bin/node

const exec = require("child_process").exec;
const stream = require("stream");
const fs = require("fs");

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

(declare-datatypes () ((Encoding
  (mk-enc (channel Channel) (field Field) (type FieldType) (binned Bool) (agg AggFunc))
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

function buildProgram(fields, query) {
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
    program += `(assert (= mark ${query.mark}Mark))`;
  }

  // add encodings
  const encs = [];
  if (query.encoding) {
    query.encoding.forEach((e, i) => {
      const enc = `e${i}`;
      program += `(declare-const ${enc} Encoding)`;
      if (e.field) {
        program += `(assert (= (field ${enc}) ${e.field}))`;
      }
      if (e.channel) {
        program += `(assert (= (channel ${enc}) ${e.channel}))`;
      }
      encs.push(enc);
    });
  }

  // add constraints

  if (encs.length === 0) {
    // we need at least one channel
    program += "(assert false)";
  } else {
    const barOrTick = `(or (= mark BarMark) (= mark TickMark))`;


    // cannot use the same channel twice
    const channels = encs.map(e => `(channel ${e})`).join(" ");
    program += `(assert (distinct ${channels}))\n`;

    // bar and tick should not use size
    const channelsSize = encs.map(e => `(= (channel ${e}) Size)`).join(" ");
    program += `(assert (=> ${barOrTick} (not (or ${channelsSize}))))\n`;

    // bar and tick mark need quantitative and not binned on X or Y
    const channelsQuant = encs.map(e => `(and (= (channel ${e}) X) (= (channel ${e}) Y) (= (type ${e}) Quantitative) (not (binned ${e})))`).join(" ");
    program += `(assert (=> ${barOrTick} (or ${channelsQuant}) ))`;

    // bar and tick mark cannot have two quantitative
    // TODO

    // text channel can only be used with text mark, and text channel is required
    const channelsText = encs.map(e => `(= (channel ${e}) Text)`).join(" ");
    program += `(assert (=> (= mark TextMark) (or ${channelsText})))`;
  }

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
  mark: "Text",
  encoding: [
    { field: "str1" },
    { field: "num1", channel: "Size" },
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
