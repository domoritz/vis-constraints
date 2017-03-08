import * as yargs from 'yargs';
import {exec} from "child_process";
import * as stream from "stream";
import * as fs from "fs";
import {ranking} from "./ranking";
import {constraints} from "./constraints";
import {assert, eq, not, or} from "./helpers";

const types = `
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
`;

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
  // const [defs, minimizeStmt] = ranking(fields, query)
  
  //program += defs;
  //program += minimizeStmt;
  
  program += solve;
  
  program += `
  (echo "Spec:")
  (get-value (mark))
  ${encs.map(e => `(get-value (${e}))`).join("\n")}
  `;
  
  return program;
}

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

        encoding[$1] = enc;
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

const argv = yargs.argv;

if (argv["o"]) {
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
    
    const vl = argv["vl"]
    
    if (vl) {
      console.log(`Writing ${vl}`);
      fs.writeFile(vl, JSON.stringify(parse(stdout)), () => {});
    } else {
      console.log(stdout);
    }
  });
  
  if (argv["d"]) {
    console.log("Writing out.z3");
    fs.writeFile("out.z3", program, () => {});
  }
  
  const stdinStream = new stream.Readable();
  
  stdinStream.push(program);  // Add data to the internal queue for users of the stream to consume
  stdinStream.push(null);   // Signals the end of the stream (EOF)
  stdinStream.pipe(child.stdin);
}
