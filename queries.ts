import {Data} from 'vega-lite/build/src/data';
import {Mark} from 'vega-lite/build/src/mark';
import {Channel} from 'vega-lite/build/src/channel';
import {Type} from 'vega-lite/build/src/type';
import {AggregateOp} from 'vega-lite/build/src/aggregate';

export type Fields = {name: string, type: string, cardinality: number}[];

export interface Query {
  data: Data
  mark?: Mark,
  encodings: {
    field?: string,
    type?: Type,
    channel?: Channel,
    binned?: boolean,
    aggregate?: AggregateOp,
    scale?: {
      log?: boolean,
      zero?: boolean
    }
  }[]
}

export const FIELDS: Fields = [{
  name: "Cylinders",
  type: "Integer",
  cardinality: 8
}, {
  name: "Acceleration",
  type: "Float",
  cardinality: 1000
}, {
  name: "Horsepower",
  type: "Float",
  cardinality: 1000
}, {
  name: "Miles_per_Gallon",
  type: "Float",
  cardinality: 1000
}, {
  name: "Displacement",
  type: "Float",
  cardinality: 1000
}, {
  name: "Weight_in_lbs",
  type: "Float",
  cardinality: 1000
}, {
  name: "Year",
  type: "Date",
  cardinality: 20
}, {
  name: "Origin",
  type: "String",
  cardinality: 3
}];

export const QUERIES: Query[] = [{
  // 0: uses many features
  data: {url: "cars.json"},
  mark: "bar",
  encodings: [
    { field: "Acceleration"},
    { field: "Horsepower", channel: "color", binned: true },
    { aggregate: "count"}
  ]
}, {
  // 1: should give us a scatter plot
  data: {url: "cars.json"},
  encodings: [
    { field: "Acceleration"},
    { field: "Horsepower"},
  ]
}, {
  // 2: should be a histogram
  data: {url: "cars.json"},
  encodings: [
    { field: "Acceleration"},
    { aggregate: "count"},
  ]
}, {
  // 3: should be a bar chart
  data: {url: "cars.json"},
  encodings: [
    { field: "Origin"},
    { field: "Horsepower"}
  ]
}, {
  // 4: some qant and some ordinal
  data: {url: "cars.json"},
  encodings: [
    { type: "quantitative"},
    { type: "ordinal"}
  ]
}, {
  // 5: should give us a colored scatter plot
  data: {url: "cars.json"},
  encodings: [
    { field: "Miles_per_Gallon"},
    { field: "Acceleration"},
    { field: "Origin"}
  ]
}, {
  // 6: should give us a tick plot
  data: {url: "cars.json"},
  encodings: [
    { field: "Origin"},
    { field: "Horsepower"}
  ]
}, {
  // 7: should be unsat
  data: {url: "cars.json"},
  encodings: [
    { field: "Origin", type: "quantitative" }
  ]
}];
