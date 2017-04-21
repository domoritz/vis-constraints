import { and, assert, assertSoft, eq, implies, not, or } from "./helpers";

export function isDimension(e: string) {
  return or(
    eq(`(type ${e})`, "Ordinal"),
    eq(`(type ${e})`, "Nominal"),
    `(binned ${e})`,
  )
}

export function isMeasure(e: string) {
  return not(isDimension(e));
}

export function constraints(encs: string[], fields: string[]) {
  const hard = [];
  const soft = [];

  function pushHard(s: string) {
    hard.push(assert(s));
  }

  function pushSoft(s: string, i: number) {
    soft.push(assertSoft(s, i));
  }
  
  const barMark = eq("mark", "BarMark");
  const textMark = eq("mark", "TextMark");
  const areaMark = eq("mark", "AreaMark");
  const ruleMark = eq("mark", "RuleMark");
  const rectMark = eq("mark", "RectMark");
  const pointMark = eq("mark", "PointMark");
  const tickMark = eq("mark", "TickMark");
  const lineMark = eq("mark", "LineMark");
  
  const shapeEncoding = encs.map(e => eq(`(channel ${e})`, "Shape"));
  const sizeEncoding = encs.map(e => eq(`(channel ${e})`, "Size"));
  const textEncoding = encs.map(e => eq(`(channel ${e})`, "Text"));
  const xEncoding = encs.map(e => eq(`(channel ${e})`, "X"));
  const yEncoding = encs.map(e => eq(`(channel ${e})`, "Y"));
  const detailEncoding = encs.map(e => eq(`(channel ${e})`, "Detail"));
  
  const aggregatedEncodings = encs.map(e => not(eq(`(agg ${e})`, "None")));
  const rawEncodings = encs.map(e => eq(`(agg ${e})`, "None"));
  const dimensionEncodings = encs.map(e => isDimension(e));
  
  // cannot use the same channel twice
  const channels = encs.map(e => `(channel ${e})`).join(" ");
  pushHard(`(distinct ${channels})`);
  
  encs.forEach(e => {
    // encoding has to use one of the fields
    const encodingField = fields.map(f =>
      eq(`(field ${e})`, `${f}Field`)
    );
    encodingField.push(eq(`(field ${e})`, "countField"));
    pushHard(or(...encodingField));

    // primitive type has to support data type
    pushHard(implies(
      or(eq(`(type (field ${e}))`, "BooleanType"), eq(`(type (field ${e}))`, "StringType")),
      not(eq(`(type ${e})`, "Quantitative"))));

    // can only bin quantitative
    pushHard(implies(`(binned ${e})`, eq(`(type ${e})`, "Quantitative")));

    // no not use scale zero with binned
    pushHard(implies(`(binned ${e})`, not(`(zero (scale ${e}))`)));

    // do not use scale zero with dimension
    pushHard(implies(isDimension(e), not(`(zero (scale ${e}))`)));

    // do not use log scale with dimension
    pushHard(implies(isDimension(e), not(`(log (scale ${e}))`)));

    // can only do one of aggregate or bin
    pushHard(not(and(`(binned ${e})`, not(eq(`(agg ${e})`, "None")))));

    // mean and sum only works for quantitative
    pushHard(implies(or(eq(`(agg ${e})`, "Mean"), eq(`(agg ${e})`, "Sum")), eq(`(type ${e})`, "Quantitative")));

    // min, max, median only works for ordinal or quantitative
    pushHard(implies(
      or(eq(`(agg ${e})`, "Min"), eq(`(agg ${e})`, "Max"), eq(`(agg ${e})`, "Median")),
      or(eq(`(type ${e})`, "Quantitative"), eq(`(type ${e})`, "Ordinal"))
    ));

    // count field (*) requires count (and vice versa)
    pushHard(eq(eq(`(field ${e})`, "countField"), eq(`(agg ${e})`, "Count")));
  
    // shape requires dimension
    pushHard(implies(eq(`(channel ${e})`, "Shape"), isDimension(e)));

    // size or text require measure
    pushHard(implies(or(eq(`(channel ${e})`, "Size"), eq(`(channel ${e})`, "Text")), isMeasure(e)));

    // categorical channel should not have too high cardinality
    pushHard(implies(and(eq(`(channel ${e})`, "Color"), eq(`(type ${e})`, "Nominal")), `(<= (cardinality (field ${e})) 20)`));

    // shape channel should not have too high cardinality
    pushHard(implies(eq(`(channel ${e})`, "Shape"), `(<= (cardinality (field ${e})) 6)`));

    // large cardinality numbers should be binned when used as ordinal
    pushHard(implies(and(eq(`(type ${e})`, "Ordinal"), `(>= (cardinality (field ${e})) 20)`), `(binned ${e})`));

    // aggregate should be used with quantitative
    pushHard(implies(not(eq(`(agg ${e})`, "None")), eq(`(type ${e})`, "Quantitative")));

    // do not use nominal for string
    pushSoft(implies(eq(`(type (field ${e}))`, "StringType"), eq(`(type ${e})`, "Nominal")), 6);

    // prefer not to use nominal or ordinal
    pushSoft(not(eq(`(type ${e})`, "Ordinal")), 1);
    pushSoft(not(eq(`(type ${e})`, "Nominal")), 2);

    // prefer not to use only non-positional encoding channels
    // TODO: this is not a great way to encode this
    pushSoft(eq(`(channel ${e})`, "X"), 1);
    pushSoft(eq(`(channel ${e})`, "Y"), 1);

    // prefer not to use binning for quantitative
    pushSoft(implies(eq(`(type ${e})`, "Quantitative"), not(`(binned ${e})`)), 1);

    // prefer to use raw
    pushSoft(eq(`(agg ${e})`, "None"), 1);
  });
  
  // old: bar mark requires quantitative scale to start at zero
  // fix: bar mark requires at least one quantitative scale to start at zero
  // should we rewrite this with isDimension?
  let xyEncs = ["getXEnc", "getYEnc"];
  const zeroScale = xyEncs.map(e => implies(
      and(
        not(`(binned ${e})`),
        eq(`(type ${e})`, "Quantitative")
      ),
      `(zero (scale ${e}))`
    ));
  pushHard(implies(barMark, and(...zeroScale)));
  
  // shape channel requires point mark
  pushHard(implies(or(...shapeEncoding), pointMark));
  
  // size only works with some marks
  pushHard(implies(or(...sizeEncoding), or(pointMark, ruleMark, textMark, lineMark)));
  
  // text channel can only be used with text mark, and text channel is required
  pushHard(eq(textMark, or(...textEncoding)));
  
  // bar and tick should not use size
  pushHard(implies(or(barMark, tickMark), not(or(...sizeEncoding))));
  
  // area and line require x and y
  pushHard(implies(or(areaMark, lineMark), and(or(...xEncoding), or(...yEncoding))));
  
  // bar, point, tick and rule require either x or y
  pushHard(implies(or(barMark, pointMark, tickMark, ruleMark), (or(...xEncoding, ...yEncoding))));
  
  // bar and tick mark needs dimension on X or Y
  const xOrYDimension = encs.map(e =>
    and(
      or(eq(`(channel ${e})`, "X"), eq(`(channel ${e})`, "Y")),
      isDimension(e)
    ));
  
  pushHard(implies(or(barMark, tickMark), or(...xOrYDimension)));

  // bar and tick requires exactly one measure on X or Y
   const xOrYMeasure = encs.map(e =>
    and(
      or(eq(`(channel ${e})`, "X"), eq(`(channel ${e})`, "Y")),
      isMeasure(e)
    ));
  
  pushHard(implies(or(barMark, tickMark), or(...xOrYMeasure)));
  
  // aggregate also should have a dimension
  pushHard(implies(or(...aggregatedEncodings), or(...dimensionEncodings)));

  // details requires aggregation
  pushHard(implies(or(...detailEncoding), or(...aggregatedEncodings)));

  // do not use log scale for bar charts
  const noLogScale = encs.map(e => implies(
      and(
        or(eq(`(channel ${e})`, "X"), eq(`(channel ${e})`, "Y")),
        eq(`(type ${e})`, "Quantitative")
      ),
      not(`(log (scale ${e}))`)
    ));
  pushHard(implies(barMark, and(...noLogScale)));

  // stacked plot should only use linear scale
  // TODO

  // do not aggregate everything
  pushSoft(or(...rawEncodings), 10);
  
  // prefer not to use the same field twice
  const allFields = encs.map(e => `(name (field ${e}))`).join(" ");
  pushSoft(`(distinct ${allFields})`, 1);

  return {hard, soft};
}