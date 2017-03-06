#! /usr/local/bin/node

import {exec} from "child_process";
import * as stream from "stream";
import * as fs from "fs";
import {ranking} from "./ranking";
import {constraints} from "./constraints";
import {assert, eq, not, or} from "./helpers";

let testRankings = false;

const types = `
(set-option :produce-unsat-cores true)
; data related types

(declare-datatypes () ((RawType 
  String Float Integer Date Boolean
)))

(declare-datatypes () ((Field 
  (mk-field (name String) (type RawType) (cardinality Int))
)))

; encoding related types

(declare-datatypes () ((Marktype 
  PointMark BarMark LineMark AreaMark TextMark TickMark RuleMark RectMark
)))

(declare-datatypes () ((Channel 
  X Y Color Size Shape Text Detail Opacity Row Column 
)))

(declare-datatypes () ((EncodingType 
  Quantitative Ordinal Nominal
)))

(declare-datatypes () ((AggFunc 
  None Count Sum Mean Median Min Max
)))

(declare-datatypes () ((Scale 
  (mk-scale (zero bool))
)))

(declare-datatypes () ((Encoding
  (mk-enc (channel Channel) (field Field) (type EncodingType) (binned Bool) (agg AggFunc) (scale Scale))
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
(get-unsat-core)
`;

function callZ3(program: string){
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

function buildProgram(fields: {name: string, type: string, cardinality: number}[], query) {
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
    (assert (= (cardinality ${name}) ${f.cardinality}))
    `;
  });
  
  // add mark type constraint
  if (query.mark) {
    program += assert(eq("mark", `${query.mark}Mark`));
  }

  // add encodings
  const encs: string[] = [];
  if (query.encoding) {
    query.encoding.forEach((e, i: number) => {
      const enc = `e${i}`;
      program += `(declare-const ${enc} Encoding)`;
      if (e.field) {
        program += assert(eq(`(name (field ${enc}))`, `"${e.field}"`));
      }
      if (e.type) {
        program += assert(eq(`(type ${enc})`, `${e.type}`));
      }
      if (e.channel) {
        program += assert(eq(`(channel ${enc})`, `${e.channel}`));
      }
      if (e.aggregate) {
        program += assert(eq(`(agg ${enc})`, `${e.aggregate}`));
      }
      if (e.binned !== undefined) {
        if (e.binned) {
          program += assert(`(binned ${enc})`);
        } else {
          program += assert(not(`(binned ${enc})`));
        }
      }

      encs.push(enc);
    });
  }

  // add constraints

  if (encs.length === 0) {
    // we need at least one channel
    program += assert("false");
  } else {
    program += constraints(encs, fields.map(f => f.name));
  }

  // FIXME: greg
  const [defs, minimizeStmt] = ranking(fields, query, encs)
  //console.log(defs);
  program += defs;
  program += minimizeStmt;

  if(testRankings){
    // should give e2 as text 
    program += assert (not ( or( 
                                 eq("(channel e0)", "Y"), 
                                 eq("(channel e0)", "X"), 
                                
                                 eq("(channel e2)", "Size")
                                 )));
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
} // END buildProgram

const fields = [{
  name: "int1",
  type: "Integer",
  cardinality: 10
}, {
  name: "int2",
  type: "Integer",
  cardinality: 100
}, {
  name: "float1",
  type: "Float",
  cardinality: 1000
}, {
  name: "float2",
  type: "Float",
  cardinality: 1000
}, {
  name: "str1",
  type: "String",
  cardinality: 3
}, {
  name: "str2",
  type: "String",
  cardinality: 5
}];

const query = {
  mark: "Bar",
  encoding: [
    { field: "str1"},
    { field: "float1", channel: "Color", binned: true },
    { aggregate: "Count"}
  ]
}

const program = buildProgram(fields, query);

if (process.argv[2] === "-o") {
  // output program instead of passing it to z3
  console.log(program);
} else if(process.argv[2] === "-rtest") {
  testRankings = true;
  let test_program = buildProgram(fields, query);
  console.log(test_program);
  callZ3(test_program);
} else {
  callZ3(program);
}