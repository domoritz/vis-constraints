
export function assert(s: string) {
  return `(assert ${s})\n\n`;
}

function implies(a: string, b: string) {
  return `(=> ${a} ${b})\n`;
}

function and(...exprs: string[]) {
  return `(and
    ${exprs.join("\n")}
  )`;
}

function or(...exprs: string[]) {
  return `(or
    ${exprs.join("\n")}
  )`;
}

export function eq(a: string, b: string) {
  return `(= ${a} ${b})`;
}

function not(s) {
  return `(not ${s})`;
}

export function hardConstraints(encs: string[]) {
    let program = "";

    const barMark = eq("mark", "BarMark");
    const symbolMark = eq("mark", "SymbolMark");
    const textMark = eq("mark", "TextMark");
    const barOrTick = or(barMark, eq("mark", "TickMark"));

    // cannot use the same channel twice
    const channels = encs.map(e => `(channel ${e})`).join(" ");
    program += assert(`(distinct ${channels})`);

    // bar mark requires scale to start at zero
    const zeroScale = encs.map(e => implies(
      and(
        or(eq(`(channel ${e})`, "X"), eq(`(channel ${e})`, "Y")),
        eq(`(type ${e})`, "Quantitative")
      ),
      `(zero (scale ${e}))`
    ));

    program += assert(implies(barMark, and(...zeroScale)))

    // bar and tick should not use size
    const channelsSize = encs.map(e => eq(`(channel ${e})`, "Size"));
    program += assert(implies(barOrTick, not(or(...channelsSize))));

    // bar and tick mark needs ordinal, nominal, or binned quantitative on X or Y
    const channelsCat = encs.map(e =>
      and(
        or(eq(`(channel ${e})`, "X"), eq(`(channel ${e})`, "Y")),
        or(
          eq(`(type ${e})`, "Ordinal"),
          eq(`(type ${e})`, "Nominal"),
          and(
            eq(`(type ${e})`, "Quantitative")),
            `(binned ${e})`
          )
        )
      );

    program += assert(implies(barOrTick, or(...channelsCat)));

    // text channel can only be used with text mark, and text channel is required
    const channelsText = encs.map(e => eq(`(channel ${e})`, "Text"));
    program += assert(eq(textMark, or(...channelsText)));

    // shape requires symbol mark
    const channelsShape = encs.map(e => eq(`(channel ${e})`, "Shape"));
    program += assert(eq(symbolMark, or(...channelsShape)));

    return program;
}