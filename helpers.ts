let id: number = 0;

export function assert(s: string) {
  //return `(assert ${s})\n\n`;
  id++;
  return `(assert (! ${s} :named c${id}))\n\n`;
}

export function assertSoft(s: string, weight: number) {
  return `(assert-soft ${s} :weight ${weight})\n\n`;
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