include "../argparse.mc"
include "ast.mc"
include "codegen-base.mc"

include "stdlib::json.mc"

-- Generates a JSON specification given the arguments passed to the compiler
-- and the lowered ProbTime AST. This specification allow us to adjust
-- properties of the system after compilation.
lang ProbTimeJson = ProbTimeAst + ProbTimeCodegenBase
  sem generateJsonSpecification : RtpplOptions -> PTProgram -> ()
  sem generateJsonSpecification options =
  | program ->
    let json = makeJsonSystemSpecification options program in
    let path = optJoinPath "system.json" options.outputPath in
    writeFile path (json2string json)

  sem makeJsonSystemSpecification : RtpplOptions -> PTProgram -> JsonValue
  sem makeJsonSystemSpecification options =
  | program ->
    let aliases = foldl addTypeAliasMapping (mapEmpty nameCmp) program.tops in
    let json = foldl (addNodeSpec aliases) (mapEmpty cmpString) program.system in

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

  sem addTypeAliasMapping : Map Name PTType -> PTTop -> Map Name PTType
  sem addTypeAliasMapping aliases =
  | PTTTypeAlias t -> mapInsert t.id (resolveTypeAlias aliases t.ty) aliases
  | _ -> aliases

  sem addNodeSpec : Map Name PTType -> Map String JsonValue -> PTNode
                 -> Map String JsonValue
  sem addNodeSpec aliases json =
  | PTNSensor t ->
    let sensorEntry = JsonArray [makeExternalJsonObject t.id t.rate] in
    let json = mapInsertWith concatJsonArray "sensors" sensorEntry json in

    -- Add information about all outgoing connections from this sensor.
    let src = Sensor {id = t.id, ty = t.ty, info = t.info} in
    let connections = JsonArray (map (makeConnectionJsonObject aliases src) t.outputs) in
    mapInsertWith concatJsonArray "connections" connections json
  | PTNActuator t ->
    let actuatorEntry = JsonArray [makeExternalJsonObject t.id t.rate] in
    mapInsertWith concatJsonArray "actuators" actuatorEntry json
  | PTNTask t ->
    let taskEntry = JsonArray [JsonObject (mapFromSeq cmpString [
      ("id", JsonString (nameGetStr t.id)),
      ("importance", JsonFloat (int2float t.importance)),
      ("minrate", JsonInt t.minDelay),
      ("maxrate", JsonInt t.maxDelay),
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
            concat acc (map (makeConnectionJsonObject aliases src) dsts))
          [] t.outputs)
    in
    mapInsertWith concatJsonArray "connections" connections json

  sem makeConnectionJsonObject : Map Name PTType -> PTPort -> PTPort -> JsonValue
  sem makeConnectionJsonObject aliases src =
  | dst ->
    let ty = resolveTypeAlias aliases (ptPortType src) in
    match computeMessageSizeByType ty with (baseSize, perParticleSize) in
    -- TODO(larshum, 2024-11-05): Add an approach for estimating an upper bound
    -- on the number of messages sent per task instance.
    let messagesPerInstance = 0.0 in
    JsonObject (mapFromSeq cmpString [
      ("from", JsonString (ptPortName src)),
      ("to", JsonString (ptPortName dst)),
      ("messageBaseSize", JsonInt (baseSize)),
      ("messagePerParticleSize", JsonInt (perParticleSize)),
      ("messagesPerInstance", JsonFloat (messagesPerInstance))
    ])

  sem computeMessageSizeByType : PTType -> (Int, Int)
  sem computeMessageSizeByType =
  | ty ->
    -- NOTE(larshum, 2024-11-05): In the current approach, all messages include
    -- two 64-bit integers representing the size of the remainder of the
    -- message (excluding itself) and a timestamp. We add this to the base cost
    -- of each message.
    match computeMessageSizeByTypeH ty with (base, perParticle) in
    (addi base 16, perParticle)

  sem computeMessageSizeByTypeH : PTType -> (Int, Int)
  sem computeMessageSizeByTypeH =
  | PTTInt _ | PTTFloat _ -> (8, 0)
  | PTTRecord {fields = fields} ->
    mapFoldWithKey
      (lam acc. lam. lam ty.
        match computeMessageSizeByTypeH ty with (base, perParticle) in
        (addi acc.0 base, addi acc.1 perParticle))
      (0, 0) fields
  | PTTDist {ty = ty, info = info} ->
    match computeMessageSizeByTypeH ty with (base, 0) then
      -- NOTE(larshum, 2024-11-05): Each sample in a distribution consists of
      -- the data of the base type plus a 64-bit floating-point weight. We have
      -- no base overhead for the distribution itself in the current encoding.
      (0, addi base 8)
    else errorSingle [info] "Found nested distribution type in JSON generation"
  | ty ->
    errorSingle [ptTypeInfo ty] "Found unsupported type in JSON generation"

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
