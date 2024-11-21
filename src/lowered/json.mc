include "../argparse.mc"
include "ast.mc"
include "codegen-base.mc"
include "task.mc"

include "stdlib::json.mc"

-- Generates a JSON specification given the arguments passed to the compiler
-- and the lowered ProbTime AST. This specification allow us to adjust
-- properties of the system after compilation.
lang ProbTimeJson =
  ProbTimeAst + ProbTimeCodegenBase + ProbTimeTaskConfigurableInfer +
  ProbTimeInterArrivalTimes

  type JsonSpecEnv = {
    configurableTasks : Set Name,
    taskArrivalTimes : Map Name (Int, Int)
  }

  sem generateJsonSpecification : RtpplOptions -> PTProgram -> ()
  sem generateJsonSpecification options =
  | program ->
    let json = makeJsonSystemSpecification options program in
    let path = optJoinPath "system.json" options.outputPath in
    writeFile path (json2string json)

  sem makeJsonSystemSpecification : RtpplOptions -> PTProgram -> JsonValue
  sem makeJsonSystemSpecification options =
  | program ->
    let env = {
      configurableTasks = findTasksWithConfigurableInfer program,
      taskArrivalTimes = findTaskInterArrivalTimes program
    } in
    let json = foldl (addNodeSpec env) (mapEmpty cmpString) program.system in

    -- NOTE(larshum, 2024-11-05): Exposes important compile-time parameters
    -- that were used to compile the ProbTime system.
    let compileopts = JsonObject (mapFromSeq cmpString [
      ("bufferSize", JsonInt options.bufferSize),
      ("outputPath", JsonString options.outputPath),
      ("file", JsonString options.file)
    ]) in
    let json = mapInsert "compileopts" compileopts json in

    -- NOTE(larshum, 2024-11-05): Represents global parameters of the system
    -- that we can reconfigure without having to recompile.
    let config = JsonObject (mapFromSeq cmpString [
      ("slowdown", JsonInt 1)
    ]) in
    let json = mapInsert "config" config json in

    JsonObject json

  sem addNodeSpec : JsonSpecEnv -> Map String JsonValue -> PTNode
                 -> Map String JsonValue
  sem addNodeSpec env json =
  | PTNSensor t ->
    let sensorEntry = JsonArray [makeExternalJsonObject t.id t.rate] in
    let json = mapInsertWith concatJsonArray "sensors" sensorEntry json in

    -- Add information about all outgoing connections from this sensor.
    let src = Sensor {id = t.id, ty = t.ty, info = t.info} in
    let connections = JsonArray (map (makeConnectionJsonObject env src) t.outputs) in
    mapInsertWith concatJsonArray "connections" connections json
  | PTNActuator t ->
    let actuatorEntry = JsonArray [makeExternalJsonObject t.id t.rate] in
    mapInsertWith concatJsonArray "actuators" actuatorEntry json
  | PTNTask t ->
    match
      match mapLookup t.id env.taskArrivalTimes with Some (mina, maxa) then
        (mina, maxa)
      else errorSingle [t.info] "Could not find arrival time bounds for task"
    with (minArrivalTime, maxArrivalTime) in
    let taskEntry = JsonArray [JsonObject (mapFromSeq cmpString [
      ("id", JsonString (nameGetStr t.id)),
      ("importance", JsonFloat 0.0),
      ("minarrival", JsonInt minArrivalTime),
      ("maxarrival", JsonInt maxArrivalTime),
      ("configurable", JsonBool (setMem t.id env.configurableTasks)),
      ("particles", JsonInt 0),
      ("budget", JsonInt 0),
      ("core", JsonInt 0)
    ])] in
    let json = mapInsertWith concatJsonArray "tasks" taskEntry json in

    -- Add information about all outgoing connections from this task.
    let connections =
      JsonArray
        (mapFoldWithKey
          (lam acc. lam label. lam dsts.
            let ty = ptPortType (head dsts) in
            let src = Task {
              id = t.id, label = label, isOutput = true, ty = ty, info = t.info
            } in
            concat acc (map (makeConnectionJsonObject env src) dsts))
          [] t.outputs)
    in
    mapInsertWith concatJsonArray "connections" connections json

  sem makeConnectionJsonObject : JsonSpecEnv -> PTPort -> PTPort -> JsonValue
  sem makeConnectionJsonObject env src =
  | dst ->
    JsonObject (mapFromSeq cmpString [
      ("from", JsonString (ptPortName src)),
      ("to", JsonString (ptPortName dst))
    ])

  sem concatJsonArray : JsonValue -> JsonValue -> JsonValue
  sem concatJsonArray lhs =
  | rhs -> concatJsonArrayH (lhs, rhs)

  sem concatJsonArrayH : (JsonValue, JsonValue) -> JsonValue
  sem concatJsonArrayH =
  | (JsonArray lhs, JsonArray rhs) -> JsonArray (concat lhs rhs)
  | _ -> error "Invalid JSON array"

  sem makeExternalJsonObject : Name -> PTExpr -> JsonValue
  sem makeExternalJsonObject id =
  | PTELiteral {const = PTCInt {value = rate}} ->
    JsonObject (mapFromSeq cmpString [
      ("id", JsonString (nameGetStr id)),
      ("rate", JsonInt rate)
    ])
  | e ->
    errorSingle [ptExprInfo e] "Rate must be an integer literal"

  sem optJoinPath : String -> String -> String
  sem optJoinPath file =
  | "" -> file
  | path -> join [path, "/", file]
end
