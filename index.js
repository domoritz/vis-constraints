#! /usr/local/bin/node

const exec = require('child_process').exec;
const stream = require('stream');

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
   Point Bar Line Area Symbol Text Tick
)))

(declare-datatypes () ((Channel 
   X Y Color Size Shape Text Detail
)))

(declare-datatypes () ((FieldType 
   Q O N
)))

(declare-datatypes () ((AggFunc 
   None Count Mean Median Min Max
)))

(declare-datatypes () ((Encoding
    (mk-enc (channel Channel) (field String) (type FieldType) (agg AggFunc))
)))
`;

const solve = `
; get output
(check-sat)
(get-model)
`;

function buildProgram() {
    let program = "";

    program += types;
    program += solve;

    return program;
}

if (process.argv[2] === "-o") {
    // output program instead of passing it to z3
    console.log(buildProgram());
} else {
    // execute in z3
    const child = exec('z3 /dev/fd/0', function (err, stdout, stderr) {
        if (err) {
            console.error(err);
        }
        if (stderr) {
            console.error(stderr);
        }
        // TODO: parse
        console.log(stdout);
    });

    const stdinStream = new stream.Readable();

    stdinStream.push(buildProgram());  // Add data to the internal queue for users of the stream to consume
    stdinStream.push(null);   // Signals the end of the stream (EOF)
    stdinStream.pipe(child.stdin);
}
