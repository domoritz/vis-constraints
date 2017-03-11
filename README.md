# vis-constraints

Vega-Lite and CompassQl as constraints.

Install dependencies with `npm install`.

Currently needs [z3 nightlies](https://github.com/Z3Prover/bin/tree/master/nightly).

## Run the complete pipeline

Run the command below and change which query to run. The queries are in `queries.ts`.

```bash
npm run run -- --query 0
```

## Debugging

Run `npm run start` to run with debug output. Add optional `--query NUMBER` to change which query to run.
