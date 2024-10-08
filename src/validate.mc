include "ast.mc"

-- NOTE(larshum, 2023-04-12): Validates the network defined in the RTPPL
-- program. This includes ensuring that all ports are used, and that they are
-- used correctly.
lang RtpplValidateSystem = RtpplAst
  syn PortId =
  | External Name
  | Internal (Name, String)

  sem cmpPortId : PortId -> PortId -> Int
  sem cmpPortId lhs =
  | rhs -> cmpPortIdH (lhs, rhs)

  sem cmpPortIdH : (PortId, PortId) -> Int
  sem cmpPortIdH =
  | (External l, External r) -> nameCmp l r
  | (Internal l, Internal r) ->
    let d = nameCmp l.0 r.0 in
    if neqi d 0 then d else cmpString l.1 r.1
  | (lhs, rhs) -> subi (constructorTag lhs) (constructorTag rhs)

  sem portIdToString : PortId -> String
  sem portIdToString =
  | External id -> nameGetStr id
  | Internal (taskId, portId) ->
    join [nameGetStr taskId, ".", portId]

  syn PortState =
  | UnusedSensorOutput Info
  | UnusedActuatorInput Info
  | UnusedTaskInput Info
  | UnusedTaskOutput Info
  | UsedSensorOutput Info
  | UsedActuatorInput Info
  | UsedTaskInput Info
  | UsedTaskOutput Info

  sem portStateInfo : PortState -> Info
  sem portStateInfo =
  | UnusedSensorOutput i -> i
  | UnusedActuatorInput i -> i
  | UnusedTaskInput i -> i
  | UnusedTaskOutput i -> i
  | UsedSensorOutput i -> i
  | UsedActuatorInput i -> i
  | UsedTaskInput i -> i
  | UsedTaskOutput i -> i

  -- OPT(larshum, 2023-03-06): Use a more efficient data structure for storing
  -- strings, such as a trie.
  type PortConfig = Map String PortState

  type PortDecls = {
    sensors : Map Name Info,
    actuators : Map Name Info,
    decls : Map Name PortConfig
  }

  type System = Map PortId PortState

  sem validateRtpplProgramSystem : RtpplProgram -> ()
  sem validateRtpplProgramSystem =
  | ProgramRtpplProgram {tops = tops, main = main} ->
    let emptyPorts = {
      sensors = mapEmpty nameCmp,
      actuators = mapEmpty nameCmp,
      decls = mapEmpty nameCmp
    } in
    let declPorts = foldl collectDeclaredPorts emptyPorts tops in
    validateSystem declPorts main

  sem collectDeclaredPorts : PortDecls -> RtpplTop -> PortDecls
  sem collectDeclaredPorts acc =
  | TemplateDefRtpplTop {id = {v = id}, body = {ports = declaredPorts}} ->
    let emptyPortConfig = mapEmpty cmpString in
    let functionDecls = foldl addPortToConfig emptyPortConfig declaredPorts in
    {acc with decls = mapInsert id functionDecls acc.decls}
  | _ -> acc

  sem insertPortErr : String -> PortState -> PortConfig -> PortConfig
  sem insertPortErr id s1 =
  | config ->
    match mapLookup id config with Some s2 then
      let psi = portStateInfo in
      errorSingle [psi s1, psi s2] "Port name already in use"
    else mapInsert id s1 config

  sem addPortToConfig : PortConfig -> RtpplPort -> PortConfig
  sem addPortToConfig config =
  | InputRtpplPort {id = {v = id}, info = i1} ->
    insertPortErr id (UnusedTaskInput i1) config
  | OutputRtpplPort {id = {v = id}, info = i1} ->
    insertPortErr id (UnusedTaskOutput i1) config

  sem addSensorOrActuatorPort : PortDecls -> RtpplExt -> PortDecls
  sem addSensorOrActuatorPort acc =
  | SensorRtpplExt {id = {v = id}, info = info} ->
    {acc with sensors = mapInsert id info acc.sensors}
  | ActuatorRtpplExt {id = {v = id}, info = info} ->
    {acc with actuators = mapInsert id info acc.actuators}

  sem validateSystem : PortDecls -> RtpplMain -> ()
  sem validateSystem declPorts =
  | MainRtpplMain {ext = ext, tasks = tasks, connections = connections} ->
    let declPorts = foldl addSensorOrActuatorPort declPorts ext in

    -- Insert port states for all sensors and actuators.
    let network = mapEmpty cmpPortId in
    let network = mapFoldWithKey insertSensor network declPorts.sensors in
    let network = mapFoldWithKey insertActuator network declPorts.actuators in

    -- Insert ports for each of the tasks based on the declared ports of the
    -- functions they are defined in terms of.
    let network = foldl (insertTaskPorts declPorts.decls) network tasks in

    -- Update the state of the ports based on the connection definitions.
    let network = foldl addConnectionToSystem network connections in

    -- Validate the resulting network.
    mapFoldWithKey validatePortState () network

  sem insertSensor : System -> Name -> Info -> System
  sem insertSensor network id =
  | info ->
    let portId = External id in
    let state = UnusedSensorOutput info in
    mapInsert portId state network

  sem insertActuator : System -> Name -> Info -> System
  sem insertActuator network id =
  | info ->
    let portId = External id in
    let state = UnusedActuatorInput info in
    mapInsert portId state network

  sem insertTaskPorts : Map Name PortConfig -> System -> RtpplTask -> System
  sem insertTaskPorts decls network =
  | TaskRtpplTask {id = {v = id}, templateId = {v = tid}, info = info} ->
    let config =
      match mapLookup tid decls with Some config then
        config
      else
        errorSingle [info] "Task is defined in terms of undefined function"
    in
    mapFoldWithKey (insertTaskPort id) network config

  sem insertTaskPort : Name -> System -> String -> PortState -> System
  sem insertTaskPort taskId network portId =
  | state ->
    let portId = Internal (taskId, portId) in
    mapInsert portId state network

  sem addConnectionToSystem : System -> RtpplConnection -> System
  sem addConnectionToSystem network =
  | ConnectionRtpplConnection {from = fromSpec, to = toSpec, info = info} ->
    let from = portSpecToPortId fromSpec in
    let to = portSpecToPortId toSpec in
    let network =
      match mapLookup from network with Some portState then
        mapInsert from (updateOutputPortState info portState) network
      else
        errorSingle [get_RtpplPortSpec_info fromSpec]
          "Reference to undefined output port"
    in
    match mapLookup to network with Some portState then
      mapInsert to (updateInputPortState info portState) network
    else
      errorSingle [get_RtpplPortSpec_info toSpec]
        "Reference to undefined input port"

  sem portSpecToPortId : RtpplPortSpec -> PortId
  sem portSpecToPortId =
  | PortSpecRtpplPortSpec {port = {v = extId}, id = None ()} ->
    External extId
  | PortSpecRtpplPortSpec {port = {v = taskId}, id = Some {v = portId}} ->
    Internal (taskId, portId)

  sem updateOutputPortState : Info -> PortState -> PortState
  sem updateOutputPortState info =
  | UnusedSensorOutput i
  | UsedSensorOutput i ->
    UsedSensorOutput i
  | UnusedTaskOutput i
  | UsedTaskOutput i ->
    UsedTaskOutput i
  | UnusedActuatorInput i
  | UnusedTaskInput i
  | UsedActuatorInput i
  | UsedTaskInput i ->
    errorSingle [i, info] "Input ports cannot be used as output"

  sem updateInputPortState : Info -> PortState -> PortState
  sem updateInputPortState info =
  | UnusedActuatorInput i ->
    UsedActuatorInput i
  | UnusedTaskInput i ->
    UsedTaskInput i
  | UsedActuatorInput i ->
    errorSingle [i, info] "Multiple outputs cannot be mapped to one actuator input"
  | UsedTaskInput i ->
    errorSingle [i, info] "Multiple outputs cannot be mapped to one task input port"
  | UnusedSensorOutput i
  | UnusedTaskOutput i
  | UsedSensorOutput i
  | UsedTaskOutput i ->
    errorSingle [i, info] "Output ports cannot be used as input"

  sem validatePortState : () -> PortId -> PortState -> ()
  sem validatePortState acc portId =
  | UnusedActuatorInput i ->
    errorSingle [i] "No task output is connected to this actuator."
  | UnusedSensorOutput i ->
    errorSingle [i] "The output from this sensor is not connected to any task"
  | UnusedTaskOutput i ->
    let msg = join ["The output port ", portIdToString portId, " is unused."] in
    errorSingle [i] msg
  | UnusedTaskInput i ->
    let msg = join ["The input port ", portIdToString portId, " is unused."] in
    errorSingle [i] msg
  | UsedSensorOutput _
  | UsedActuatorInput _
  | UsedTaskInput _
  | UsedTaskOutput _ ->
    ()
end

-- NOTE(larshum, 2023-04-12): Ensures that names of tasks and names of ports
-- within each declaration are unique.
lang RtpplValidateNames = RtpplAst
  sem validateRtpplProgramNames : RtpplProgram -> ()
  sem validateRtpplProgramNames =
  | ProgramRtpplProgram {tops = tops, main = main} ->
    distinctTaskNames main;
    iter distinctPortNames tops

  -- Ensures that all declared tasks are given distinct names.
  sem distinctTaskNames : RtpplMain -> ()
  sem distinctTaskNames =
  | MainRtpplMain {tasks = tasks} ->
    let addUniqueName = lam acc. lam task.
      match task with TaskRtpplTask {id = {v = id}, info = info} in
      match mapLookup id acc with Some prevInfo then
        errorSingle [prevInfo, info] "Multiple tasks have the same name"
      else
        mapInsert id info acc
    in
    foldl addUniqueName (mapEmpty nameCmp) tasks;
    ()

  sem distinctPortNames : RtpplTop -> ()
  sem distinctPortNames =
  | TemplateDefRtpplTop {id = {v = id}, body = {ports = ports}} ->
    let addUniqueName = lam acc. lam port.
      match portIdAndInfo port with (portId, info) in
      match mapLookup portId acc with Some prevInfo then
        errorSingle [prevInfo, info]
          (join ["Multiple ports of task ", nameGetStr id, " are named ", portId])
      else
        mapInsert portId info acc
    in
    foldl addUniqueName (mapEmpty cmpString) ports;
    ()
  | _ -> ()

  sem portIdAndInfo : RtpplPort -> (String, Info)
  sem portIdAndInfo =
  | InputRtpplPort {id = {v = id}, info = info}
  | OutputRtpplPort {id = {v = id}, info = info} ->
    (id, info)
end

lang RtpplValidate = RtpplValidateSystem + RtpplValidateNames
  sem validateRtpplProgram : RtpplProgram -> ()
  sem validateRtpplProgram =
  | p & (ProgramRtpplProgram {tops = tops, main = main}) ->
    validateRtpplProgramNames p;
    validateRtpplProgramSystem p
end
