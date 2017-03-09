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
  let program = "";
  
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
  program += assert(`(distinct ${channels})`);
  
  encs.forEach(e => {
    // encoding has to use one of the fields
    const encodingField = fields.map(f =>
      eq(`(field ${e})`, `${f}Field`)
    );
    encodingField.push(eq(`(field ${e})`, "countField"));
    program += assert(or(...encodingField));

    // primitive type has to support data type
    program += assert(implies(
      or(eq(`(type (field ${e}))`, "Boolean"), eq(`(type (field ${e}))`, "String")),
      not(eq(`(type ${e})`, "Quantitative"))));

    // can only bin quantitative
    program += assert(implies(`(binned ${e})`, eq(`(type ${e})`, "Quantitative")));

    // no not use scale 0 with binned
    program += assert(implies(`(binned ${e})`, not(`(zero (scale ${e}))`)));

    // can only do one of aggregate or bin
    program += assert(not(and(`(binned ${e})`, not(eq(`(agg ${e})`, "None")))))

    // mean and sum only works for quantitative
    program += assert(implies(or(eq(`(agg ${e})`, "Mean"), eq(`(agg ${e})`, "Sum")), eq(`(type ${e})`, "Quantitative")));

    // min, max, median only works for ordinal or quantitative
    program += assert(implies(
      or(eq(`(agg ${e})`, "Min"), eq(`(agg ${e})`, "Max"), eq(`(agg ${e})`, "Median")),
      or(eq(`(type ${e})`, "Quantitative"), eq(`(type ${e})`, "Ordinal"))
    ));

    // count field (*) requires count (and vice versa)
    program += assert(eq(eq(`(field ${e})`, "countField"), eq(`(agg ${e})`, "Count")));
  
    // shape requires dimension
    program += assert(implies(eq(`(channel ${e})`, "Shape"), isDimension(e)));

    // size or text require measure
    program += assert(implies(or(eq(`(channel ${e})`, "Size"), eq(`(channel ${e})`, "Text")), isMeasure(e)));

    // categorical channel should not have too high cardinality
    program += assert(implies(and(eq(`(channel ${e})`, "Color"), eq(`(type ${e})`, "Nominal")), `(<= (cardinality (field ${e})) 20)`));

    // shape channel should not have too high cardinality
    program += assert(implies(eq(`(channel ${e})`, "Shape"), `(<= (cardinality (field ${e})) 6)`));
  });
  
  // bar mark requires quantitative scale to start at zero
  const zeroScale = encs.map(e => implies(
      and(
        or(eq(`(channel ${e})`, "X"), eq(`(channel ${e})`, "Y")),
        eq(`(type ${e})`, "Quantitative")
      ),
      `(zero (scale ${e}))`
    ));
  program += assert(implies(barMark, and(...zeroScale)))
  
  // shape channel requires point mark
  program += assert(implies(or(...shapeEncoding), pointMark));
  
  // size only works with some marks
  program += assert(implies(or(...sizeEncoding), or(pointMark, ruleMark, textMark, lineMark)))
  
  // text channel can only be used with text mark, and text channel is required
  program += assert(eq(textMark, or(...textEncoding)));
  
  // bar and tick should not use size
  program += assert(implies(or(barMark, tickMark), not(or(...sizeEncoding))));
  
  // area and line require x and y
  program += assert(implies(or(areaMark, lineMark), and(or(...xEncoding), or(...yEncoding))));
  
  // bar, point, tick and rule require either x or y
  program += assert(implies(or(barMark, pointMark, tickMark, ruleMark), (or(...xEncoding, ...yEncoding))));
  
  // bar and tick mark needs dimension on X or Y
  const xOrYDimension = encs.map(e =>
    and(
      or(eq(`(channel ${e})`, "X"), eq(`(channel ${e})`, "Y")),
      isDimension(e)
    ));
  
  program += assert(implies(or(barMark, tickMark), or(...xOrYDimension)));

  // bar and tick requires exactly one measure on X or Y
   const xOrYMeasure = encs.map(e =>
    and(
      or(eq(`(channel ${e})`, "X"), eq(`(channel ${e})`, "Y")),
      isMeasure(e)
    ));
  
  program += assert(implies(or(barMark, tickMark), or(...xOrYMeasure)));
  
  // aggregate also should have a dimension
  program += assert(implies(or(...aggregatedEncodings), or(...dimensionEncodings)));

  // do not use log scale for bar charts
  // TODO

  // details requires aggregation
  program += assert(implies(or(...detailEncoding), or(...aggregatedEncodings)))

  // stacked plot should only use linear scale
  // TODO

  // no not aggregate everything, TODO: make soft
  // program += assertSoft(or(...rawEncodings), 1);
  
  // TODO: prefer not to use only non-positional encoding channels
  // TODO: prefer not to use the same field twice

  return program;
}
