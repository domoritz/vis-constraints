function ite_from_dict(getValueExpr, dict, lastElseValue = 10000){

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

      return `(ite (= ${getValueExpr} ${key} )
                ${value}
                ${helper(tail)}
              )`;
    }
  };

   return helper(dict.entries());
}


function oldEncName(enc, i){
  return `old_enc${i}`;
}
function newEncName(enc, i){
  return `new_enc${i}`;
}

function soft_constraints(fields, query) {
  let encPenaltyFunctionDefinitions = [];
  let penaltyFunctionDefinitions = [];
  let penaltyFunctionNames = [];

  const encs = [];
  query.encoding.forEach((e, i) => {
    const enc = `e${i}`;
    encs.push(enc);
  });


  // the following penalties are copy-pasted from
  // compassql/src/ranking/effectiveness/channel.ts on feb 8
  // commit e8023aec8bd12c65bfddf36a1866dfd13869fa2d
 
  const TERRIBLE = 10;
  // x = y > size > color (ramp) > text > opacity >>> detail > shape ~ strokeDash ~ row = column
  const continuous_quant_penalties = {
    // copy-pasted from Ham's code, doesn't match the doc above
      x: 0,
      y: 0,
      size: 0.575,
      color: 0.725,  // Middle between 0.7 and 0.75
      text: 2,
      opacity: 3,

      shape: TERRIBLE,
      row: TERRIBLE,
      column: TERRIBLE,
      detail: 2 * TERRIBLE
  };

  // x = y > size > color (ramp) > text > row = column >>  opacity > shape ~ strokeDash > detail
  const discretized_ordinal_penalties = extend({}, continuous_quant_penalties, {
      row: 0.75,
      column: 0.75,

      shape: 3.1,
      text: 3.2,
      detail: 4
  });

  // x = y > color (hue) > shape ~ strokeDash > text > row = column >> detail >> size > opacity
  const nominal_penalties = {
      x: 0,
      y: 0,
      color: 0.6, // TODO: make it adjustable based on preference (shape is better for black and white)
      shape: 0.65,
      row: 0.7,
      column: 0.7,
      text: 0.8,

      detail: 2,
      size: 3,
      opacity: 3.1
  };

  let penaltyFunctionName = "type_channel_penalty";
  let type_channel_penalty = `(define-fun ${penaltyFunctionName} ((e Encoding)) Int

      ; (Continuous) Quantitative / Temporal Fields
      (ite (or 
              (= (type e) Quantitative)
           )
           ${ite_from_dict("e", continuous_quant_penalties)}
           
           ; else Discretized Quantitative (Binned) / Temporal Fields / Ordinal
           (ite (or 
                   ;(= (type e) Binned) not yet in types
                   (= (type e) Ordinal)
                )
                ${ite_from_dict("e", discretized_ordinal_penalties)}

                ; else it is nominal
                ${ite_from_dict("e", nominal_penalties)}
           )
      )
   )`;
  penaltyFunctionDefinitions.push(type_channel_penalty);
  penaltyFunctionNames.push(penaltyFunctionName);

  // more penalty functions go here that are f(encoding)
  


  // now we can have any other penalty functions we need
  // like if we want one that is comparisonPenalty(oldEncoding, newEncoding)
 

  // penalties hold the expression that refers
  // to z3 functions
  const penaltyStatements = [];
  encs.forEach((enc, i) => {
     penaltyFunctionNames.forEach( (pf, j) => {
       // make each constraint
       penaltyStatements.push( `(${pf} ${newEncName(enc,i)} )` );
       
       /* // if want to do compared to old solution iteratively
       penaltyStatements.push(
         `(- (${pf} ${oldEncName(enc,i)})
              (${pf} ${newEncName(enc,i)}) )`);
       });
       */
     });
  });

  let minimize_stmt = `(minimize (+ ${penaltyStatements.join(" ")}))`;

  // if deisred, we can add a constraint for
  // sum of the penalties for old > sum of the penalties for the new
  // but I'm not including that now, since this should just minimize it

  let definitions = encPenaltyFunctionDefinitions.join(" ");

  return [definitions, minimize_stmt];

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
