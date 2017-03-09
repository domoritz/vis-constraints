import * as yargs from 'yargs';
import {exec} from "child_process";
import * as stream from "stream";
import * as fs from "fs";
import {ranking} from "./ranking";
import {constraints} from "./constraints";
import {assert, eq, not, or} from "./helpers";

// parse args
const argv = yargs.argv;

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
${assert(eq("(name countField)", '"*"'))}
${assert(eq("(type countField)", "Integer"))}
`

const markDeclaration = `
(declare-const mark Marktype)
`

function solve(getModel: boolean, getUnsatCore: boolean){
  let solve = `
    ; get output
    (check-sat)
    `;
  if (getModel){
    solve+=`
      (get-model)`
  }
  if (getUnsatCore){
    solve+=`
      (get-unsat-core)`
  }
  return solve;
}

function callZ3(program: string, callback: (output: string) => void) {
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

    callback(stdout);
  });

  const stdinStream = new stream.Readable();
  
  stdinStream.push(program);  // Add data to the internal queue for users of the stream to consume
  stdinStream.push(null);   // Signals the end of the stream (EOF)
  stdinStream.pipe(child.stdin);
}

function buildProgram(fields: {name: string, type: string, cardinality: number}[], query, produceUnsatCore: boolean) {
  let program = "";
  
  program += types;
  program += markDeclaration;
  program += countField;
  
  // add fields
  fields.forEach(f => {
    const name = f.name + "Field";
    program += `(declare-const ${name} Field)
    `;
    program += assert(eq(`(name ${name})`, `"${f.name}"`)) + "\n";
    program += assert(eq(`(type ${name})`, `${f.type}`)) + "\n";
    program += assert(eq(`(cardinality ${name})`, `${f.cardinality}`)) + "\n";
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
  
  if (!produceUnsatCore) {
    const [defs, minimizeStmt] = ranking(fields, query, encs)
    //console.log(defs);
    program += defs;
    program += minimizeStmt;
  }

  if (argv["r"]){
    // should give e2 as text 
    program += assert (not ( or( 
                                 eq("(channel e0)", "Y"), 
                                 eq("(channel e0)", "X"), 
                                
                                 eq("(channel e2)", "Size")
                                 )));
  }

  program += solve(true, produceUnsatCore);

  program += `
  (echo "Spec:")
  (get-value (mark))
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

function makeIterator(array: string[]) {
  let nextIndex = 0;
  
  return {
    next: () => {
      return nextIndex < array.length ?
      {value: array[nextIndex++], done: false} :
      {value: '', done: true};
    }
  };
}

function parse(stdout) {
  const lines = makeIterator(stdout.split('\n'));
  
  let marktype = '';
  let encoding = {};

  let next = lines.next();

  // find marktype def
  while (next.value !== "Spec:" && !next.done) {
    next = lines.next();
  }

  if (next.done) {
    throw new Error("No marktype found");
  }
  
  next = lines.next();
  (next.value.replace as any)(
    /\(\(mark (\w+)Mark\)\)/gi,
    (_, $1) => {
      marktype = $1.toLowerCase();
    }
  )
  next = lines.next();

  while (!next.done) {
    let line = next.value;
    next = lines.next();
    while (!next.done && !next.value.startsWith("((e")) {
      line += ` ${next.value.trim()}`;
      next = lines.next();
    }

    (line.replace as any)(
      // ((e0 (mk-enc     X (mk-field    "str1"     String   3) Ordinal false   Min (mk-scale   true))))
      //                  $1               $2         $3    $4      $5    $6    $7               $8
      /\(\(e\d* \(mk-enc (\w+) \(mk-field "(\w+|\*)" (\w+) (\d+)\) (\w+) (\w+) (\w+) \(mk-scale (\w+)\)\)\)\)/gi,
      (_, $1, $2, $3, $4, $5, $6, $7, $8) => {
        const enc: any = {
          field: $2,
          type: $5.toLowerCase()
        }

        if ($6 !== "true") {
          enc.bin = true;
        }

        if ($7 !== "None") {
          enc.aggregate = $7.toLowerCase()
        }

        if ($8 !== "true") {
          enc.scale = {zero: true};
        }

        encoding[$1.toLowerCase()] = enc;
      }
    )
  }

  const spec = {
    mark: marktype,
    encoding: encoding
  };

  console.log(spec);

  return spec;
}

function run(produceUnsatCore) {
  const program = buildProgram(fields, query, produceUnsatCore);

  if (argv["d"]) {
    console.log("Writing out.z3");
    const program = buildProgram(fields, query, false);
    fs.writeFile("out.z3", program, () => {});
  }

  callZ3(program, (output) => {
    if (!produceUnsatCore && output.startsWith("unsat")) {
      console.log("Program was unsat")
      return run(true);
    }

    if (argv["v"]) {
      console.log("Output from z3:")
      console.log(output);
    }

    if (!produceUnsatCore) {
      const vl = argv["vl"]
      if (vl) {
        console.log(`Writing ${vl}`);
        fs.writeFile(vl, JSON.stringify(parse(output)), () => {});
      }
    }
  });
}

run(false);
