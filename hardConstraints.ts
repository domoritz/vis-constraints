
export function assert(s: string) {
  return `(assert ${s})\n\n`;
}

export function implies(a: string, b: string) {
  return `(=> ${a} ${b})\n`;
}

export function and(...exprs: string[]) {
  return `(and
  ${exprs.join("\n")}
  )`;
}

export function or(...exprs: string[]) {
  return `(or
  ${exprs.join("\n")}
  )`;
}

export function eq(a: string, b: string) {
  return `(= ${a} ${b})`;
}

export function not(s) {
  return `(not ${s})`;
}

function isDimension(e: string) {
  return or(
    eq(`(type ${e})`, "Ordinal"),
    eq(`(type ${e})`, "Nominal"),
    `(binned ${e})`,
  )
}

export function hardConstraints(encs: string[]) {
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

  // can only bin quantitative
  encs.forEach(e => {
    program += assert(implies(`(binned ${e})`, eq(`(type ${e})`, "Quantitative")));
  });

  // mean only works for quantitative
  encs.forEach(e => {
    program += assert(implies(eq(`(agg ${e})`, "Mean"), eq(`(type ${e})`, "Quantitative")));
  });

  // count field (*) requires count
  encs.forEach(e => {
    program += assert(eq(eq(`(field ${e})`, "countField"), eq(`(agg ${e})`, "Count")));
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
      not(isDimension(e))
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
  program += assert(or(...rawEncodings));

  return program;
}