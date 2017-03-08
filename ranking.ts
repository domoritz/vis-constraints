import { and, assert, assertSoft, eq, implies, not, or } from "./helpers";
import {isDimension, isMeasure } from "./constraints";

function iteFromDict(getValueExpr, dict, lastElseValue = 10000){

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

      return `(ite (= ${getValueExpr} ${capitalize(key)} ) ${value}
                ${helper(tail)})`;
    }
  };

   return helper((Object as any).entries(dict));
}

/*
greg: penalty functions with maximize let us express:
  if enough constraints at a "lower level" of priority are violated
  this should override constraints at a higher level
  in terms of hierarchies (like the channel_penalty)

  expressing the channel penalty as 8 different constraints, we can't
  "group them together" to refer to their value and weight that value 
    (it can be done but have to do the multiplication into the weight, and
     that weight isn't a solved for variable, it is defined before the program runs
     
greg: how to do it with soft constraints
for the single valued penalty functions
    (= (channel e1) key) weight: value

*/

function capitalize(s){
  return s[0].toUpperCase() + s.slice(1) 
}

function oldEncName(enc, i){
  return `old_enc${i}`;
}
function newEncName(enc, i){
  return `new_enc${i}`;
}

// https://github.com/vega/compassql/tree/master/src/ranking
// why not use http://rise4fun.com/z3opt/tutorial/ ?

export function ranking(fields, query, encs) {
  let penaltyFunctionDefinitions: string[]  = [];
  let penaltyFunctionNames: string[]  = [];

  // the following penalties are copy-pasted from
  // compassql/src/ranking/effectiveness/channel.ts on feb 8
  // commit e8023aec8bd12c65bfddf36a1866dfd13869fa2d
 
  const TERRIBLE = 1000;

  // From Greg: to get Int arithmetic in z3, I moved decimal
  //   two places to right and rounded up
  // x = y > size > color (ramp) > text > opacity >>> detail > shape ~ strokeDash ~ row = column
  const continuous_quant_penalties = {
    // copy-pasted from Ham's code, doesn't match the doc above
      x: 0,
      y: 0,
      size: 58,
      color: 73,  // Middle between 0.7 and 0.75
      text: 200,
      opacity: 300,

      shape: TERRIBLE,
      row: TERRIBLE,
      column: TERRIBLE,
      detail: 2 * TERRIBLE
  };

  // x = y > size > color (ramp) > text > row = column >>  opacity > shape ~ strokeDash > detail
  const discretized_ordinal_penalties = (Object as any).assign({
      row: 75,
      column: 75,

      shape: 310,
      text: 320,
      detail: 400
  }, continuous_quant_penalties);

  // x = y > color (hue) > shape ~ strokeDash > text > row = column >> detail >> size > opacity
  const nominal_penalties = {
      x: 0,
      y: 0,
      color: 60, // TODO: make it adjustable based on preference (shape is better for black and white)
      shape: 65,
      row: 70,
      column: 70,
      text: 80,

      detail: 200,
      size: 300,
      opacity: 310
  };

  let penaltyFunctionName = "type_channel_penalty";
  let typeChannelPenalty = `(define-fun ${penaltyFunctionName} ((e Encoding)) Int

      ; (Continuous) Quantitative / Temporal Fields
      (ite (or 
              (= (type e) Quantitative)
           )
           ${iteFromDict("(channel e)", continuous_quant_penalties)}
           
           ; else Discretized Quantitative (Binned) / Temporal Fields / Ordinal
           (ite (or 
                   ;(= (type e) Binned) not yet in types
                   (= (type e) Ordinal)
                )
                ${iteFromDict("(channel e)", discretized_ordinal_penalties)}

                ; else it is nominal
                ${iteFromDict("(channel e)", nominal_penalties)}
           )
      )
   )`;
  penaltyFunctionDefinitions.push(typeChannelPenalty);
  penaltyFunctionNames.push(penaltyFunctionName);

  // more penalty functions go here that are f(encoding)
  
  // Greg: looks like ham's types have changed a bit?
  // compassql/src/ranking/effectiveness/type.ts

  // compassql/src/ranking/effectiveness/sizechannel.ts
  
  // if mark bar and channel size, penalty 200
  const size_channel_penalties_by_mark = {
      barMark: 200,
      tickMark: 200,
  };
  penaltyFunctionName = "size_channel_penalty";
  typeChannelPenalty = `(define-fun ${penaltyFunctionName} ((e Encoding)) Int
      (ite ${eq("(channel e)", "Size")}
           ${iteFromDict("mark", size_channel_penalties_by_mark, 0)}
           0
      )
   )`;
  penaltyFunctionDefinitions.push(typeChannelPenalty);
  penaltyFunctionNames.push(penaltyFunctionName);

  // mark compassql/src/ranking/effectiveness/mark.ts
  // TODO: ask ham to open compassql and use console to output the table directly
  // will be easier to parse the full table than copy-paste it's generating logic here
  // double-check with ham that it's a static table (seems to be so)

  // compassql/src/ranking/effectiveness/dimension.ts
  //  Penalize if facet channels are the only dimensions

  // if there is an aggregation  if  (not (= (agg enc) None)
    // find the encoding that ... ? ask ham

  encs.forEach((enc, i) => {


  });
  
  // compassql/src/ranking/effectiveness/facet.ts
  // effectiveness score for preferred facet
  // Greg: we don't have preferred facet I think?
  // we would just enter that as an assertion for having it as row or column directly
  // in the query part
  // Ham just does penalty of 1 for the "non-preferred" opposite eg just col or row



  // now we can have any other penalty functions we need
  // like if we want one that is comparisonPenalty(oldEncoding, newEncoding)
 

  // penalties hold the expression that refers
  // to z3 functions
  const penaltyStatements: string[]  = [];
  encs.forEach((enc, i) => {
     penaltyFunctionNames.forEach( (pf, j) => {
       // make each constraint
       penaltyStatements.push( `(${pf} ${enc} )` );
       
       /* // if want to do compared to old solution iteratively
       penaltyStatements.push(
         `(- (${pf} ${oldEncName(enc,i)})
              (${pf} ${newEncName(enc,i)}) )`);
       });
       */
     });
  });

  // single functions


  let minimizeStmt = `(minimize (+ ${penaltyStatements.join(" ")}))`;

  // if deisred, we can add a constraint for
  // sum of the penalties for old > sum of the penalties for the new
  // but I'm not including that now, since this should just minimize it

  let definitions = penaltyFunctionDefinitions.join(" ");

  return [definitions, minimizeStmt];

  // can also solve for other conditions
  // START PARETO OPTIMAL
  /*
  const penaltyStatements = [];
  encs.forEach((enc, i) => {
     penaltyFunctionNames.forEach( (pf, j) => {
     // make each constraint
     penaltyStatements.push(
       `(>= (${pf} ${oldEncName(enc)})
            (${pf} ${newEncName(enc)}) )`);
     });
  });
  */
  // 
  // sum of the penalties for old > sum of the penalties for the new
  //
  // END PARETO OPTIMAL
  //
  // or can use it via minimize the sum of the penalties
  //
  // START MINIMIZE OVERALL
  //
  // (assert ${sum of the old penalties} > ${expression for sum of penalties for new})
  //
  // (minimize ${expression for sum of penalties for new})
  // 
  // one way to encode that last statement is
  // to_minimize_expressions += `(- (${pf} oldEnc) (${pf} newEnc))`
  // solver_minimize = `(minimize (+ ${to_minimize_expressions.join(" ")}))`;
   
}
