include "ast.mc"

-- NOTE(larshum, 2024-10-30): Validates the system defined in the ProbTime AST.
-- This includes validating that:
--  1. All sensors are used at least once.
--  2. All actuators have exactly one incoming connection.
--  3. All input ports have exactly one incoming connection.
--  4. All output ports are used at least once.
--  5. The types of connected ports are equal.
lang ProbTimeValidateSystem = ProbTimeAst
  sem collectTemplatePorts : Map Name ([PTPortDecl], [PTPortDecl]) -> PTTop
                          -> Map Name ([PTPortDecl], [PTPortDecl])
  sem collectTemplatePorts acc =
  | PTTFunDef {id = id, funKind = PTKTemplate {inputs = inputs, outputs = outputs}} ->
    mapInsert id (inputs, outputs) acc
  | _ -> acc

  sem validateNode : Map Name ([PTPortDecl], [PTPortDecl]) -> PTNode -> ()
  sem validateNode templatePorts =
  | PTNSensor {id = id, outputs = outputs, ty = ty, info = info} ->
    validatePort outputs (Sensor {id = id, ty = ty, info = info})
  | PTNActuator {id = id, inputs = inputs, ty = ty, info = info} ->
    validatePort inputs (Actuator {id = id, ty = ty, info = info})
  | PTNTask {id = id, template = template, inputs = inputs, outputs = outputs, info = info} ->
    let idStr = nameGetStr id in
    -- Validate that all ports of a task are used. We do this by looking up the
    -- ports declared in the template from which the task is instantiated.
    let inputLabels = setOfSeq cmpString (mapKeys inputs) in
    let outputLabels = setOfSeq cmpString (mapKeys outputs) in
    (match mapLookup template templatePorts with Some (inputs, outputs) then
      let unusedInputs = filterLabels inputLabels inputs in
      (if null unusedInputs then ()
      else
        let infos = map (lam p. p.info) unusedInputs in
        errorSingle infos (join ["Found unused input ports of task ", idStr]));
      let unusedOutputs = filterLabels outputLabels outputs in
      (if null unusedOutputs then ()
      else
        let infos = map (lam p. p.info) unusedOutputs in
        errorSingle infos (join ["Found unused output ports of task ", idStr]))
    else
      errorSingle [info] (join [
        "Task ", idStr, " refers to unknown template ", nameGetStr template ]));

    let validateInputPort = lam label. lam inputs.
      let ty = ptPortType (head inputs) in
      let target = Task {
        id = id, label = label, isOutput = false, ty = ty, info = info
      } in
      validatePort inputs target
    in
    mapMapWithKey validateInputPort inputs;

    let validateOutputPort = lam label. lam outputs.
      let ty = ptPortType (head outputs) in
      let target = Task {
        id = id, label = label, isOutput = true, ty = ty, info = info
      } in
      validatePort outputs target
    in
    mapMapWithKey validateOutputPort outputs;
    ()

  sem filterLabels : Set String -> [PTPortDecl] -> [PTPortDecl]
  sem filterLabels labelSet =
  | [p] ++ ports ->
    if setMem p.label labelSet then filterLabels labelSet ports
    else cons p (filterLabels labelSet ports)
  | [] -> []

  sem validatePort : [PTPort] -> PTPort -> ()
  sem validatePort connections =
  | Sensor {id = id, ty = ty, info = info} ->
    validateConnectionTypes info ty connections;
    (if null connections then
      errorSingle [info] (join ["Sensor ", nameGetStr id, " is unused."])
    else ());
    validateAllInput connections
  | Actuator {id = id, ty = ty, info = info} ->
    validateConnectionTypes info ty connections;
    (if null connections then
      errorSingle [info] (join ["Actuator ", nameGetStr id, " is unused."])
    else if gti (length connections) 1 then
      errorSingle [info] (join ["Actuator ", nameGetStr id, " is connected to multiple output ports."])
    else ());
    validateAllOutput connections
  | Task {id = id, label = label, isOutput = o, ty = ty, info = info} ->
    validateConnectionTypes info ty connections;
    (if null connections then
      errorSingle [info] (join ["Port ", nameGetStr id, ".", label, " is unused."])
    else if gti (length connections) 1 then
      if not o then
        errorSingle [info] (join ["Input port ", nameGetStr id, ".", label,
                                  " is connected to multiple output ports."])
      else ()
    else ());
    if o then validateAllInput connections
    else validateAllOutput connections

  -- Validate that all given ports connected to an output port are input ports.
  sem validateAllInput : [PTPort] -> ()
  sem validateAllInput =
  | [p] ++ ports ->
    if isOutputPort p then
      errorSingle [ptPortInfo p] (join ["Cannot use port ", ptPortName p, " as an input port."])
    else validateAllInput ports
  | [] -> ()

  -- Validate that all given ports connected to an input port are output ports.
  sem validateAllOutput : [PTPort] -> ()
  sem validateAllOutput =
  | [p] ++ ports ->
    if isInputPort p then
      errorSingle [ptPortInfo p] (join ["Cannot use port ", ptPortName p, " as an output port."])
    else ()
  | [] -> ()

  sem validateConnectionTypes : Info -> PTType -> [PTPort] -> ()
  sem validateConnectionTypes info ty =
  | [p] ++ ports ->
    if eqPTType ty (ptPortType p) then validateConnectionTypes info ty ports
    else errorSingle [info] "Invalid type of connected port"
  | [] -> ()
end

-- NOTE(larshum, 2024-11-05): Validate that the names used for sensors,
-- actuators, and tasks in the system specification are all distinct.
lang ProbTimeValidateNames = ProbTimeAst
  sem ensureDistinctSystemNames : PTMain -> ()
  sem ensureDistinctSystemNames =
  | nodes ->
    foldl validateDistinctSystemName (mapEmpty nameCmp) nodes;
    ()

  sem validateDistinctSystemName : Map Name Info -> PTNode -> Map Name Info
  sem validateDistinctSystemName defs =
  | PTNSensor {id = id, info = info}
  | PTNActuator {id = id, info = info}
  | PTNTask {id = id, info = info} ->
    match mapLookup id defs with Some i2 then
      errorSingle [info, i2]
        (join ["Found multiple system declarations with name ", nameGetStr id])
    else mapInsert id info defs
end

lang ProbTimeValidate = ProbTimeValidateSystem + ProbTimeValidateNames
  sem validateProbTimeProgram : PTProgram -> ()
  sem validateProbTimeProgram =
  | {tops = tops, system = system} ->
    let templatePorts = foldl collectTemplatePorts (mapEmpty nameCmp) tops in
    map (validateNode templatePorts) system;
    ensureDistinctSystemNames system
end
