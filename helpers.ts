import { Mark } from 'vega-lite/build/src/mark';
import { Channel } from 'vega-lite/build/src/channel';

export function capitalizeFirstLetter(string: string) {
    return string.charAt(0).toUpperCase() + string.slice(1);
}

let id: number = 0;

export function assert(s: string, name?: string) {
  // return `(assert ${s})\n\n`;
  return `(assert (! ${s} :named c${name || id++}))\n\n`;
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

export function mark(m: Mark) {
  return eq("mark", capitalizeFirstLetter(m) + "Mark");
}

// TODO: make e Encoding
export function channel(e: string, c: Channel) {
  return eq(`(channel ${e})`, capitalizeFirstLetter(c) + "Channel");
}

// TODO: add aggregate, type, ...

export function iteFromDictFlipKeyValue(getValueExpr, dict, lastElseValue = "10000"){

  // dict should be exhaustive
  // todo: lowp check values in dict are proper
  
  /*
   *  Recurse through dict
   * */
  const helper = ([head, ...tail]) => {
    if (head === undefined)
      return `${lastElseValue}`;
    else {
      const [key, value] = head;

      return `(ite (= ${getValueExpr} ${value} ) ${key}
                ${helper(tail)})`;
    }
  };

   return helper((Object as any).entries(dict));
}