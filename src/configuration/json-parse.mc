include "digraph.mc"
include "json.mc"

include "definitions.mc"

let jsonFail = lam. error "Error while reading system specification file"

let jsonUnwrap = lam o.
  match o with Some v then v
  else jsonFail ()

let jsonLookup : String -> Map String JsonValue -> JsonValue =
  lam key. lam kvs.
  jsonUnwrap (mapLookup key kvs)

let parseSystemSpecJson = lam systemSpecPath.
  let str = readFile systemSpecPath in
  match jsonParse str with Left json then
    json
  else jsonFail ()

let updateTasks : JsonValue -> [TaskData] -> JsonValue = lam json. lam tasks.
  let tasksMap = mapFromSeq cmpString (map (lam t. (t.id, t)) tasks) in
  let updateTask : JsonValue -> JsonValue = lam taskJson.
    match taskJson with JsonObject kvs then
      let taskId =
        match jsonLookup "id" kvs with JsonString s then s
        else jsonFail ()
      in
      match mapLookup taskId tasksMap with Some t then
        let mapping = [
          ("id", jsonSerializeString t.id),
          ("importance", jsonSerializeFloat t.importance),
          ("minarrival", jsonSerializeInt t.period),
          ("maxarrival", jsonSerializeInt t.period),
          ("configurable", jsonSerializeBool t.configurable),
          ("particles", jsonSerializeInt t.particles),
          ("budget", jsonSerializeInt t.budget),
          ("core", jsonSerializeInt t.core)
        ] in
        JsonObject (mapFromSeq cmpString mapping)
      else jsonFail ()
    else jsonFail ()
  in
  match json with JsonObject kvs then
    let tasksJson =
      let obj = jsonLookup "tasks" kvs in
      match obj with JsonArray taskKvs then
        JsonArray (map updateTask taskKvs)
      else jsonFail ()
    in
    JsonObject (mapInsert "tasks" tasksJson kvs)
  else jsonFail ()

let deserializeTasks : JsonValue -> [TaskData] = lam tasks.
  let deserializeTask = lam t.
    match t with JsonObject kvs then
      let id = jsonUnwrap (jsonDeserializeString (jsonLookup "id" kvs)) in
      let minrate = jsonUnwrap (jsonDeserializeInt (jsonLookup "minarrival" kvs)) in
      let maxrate = jsonUnwrap (jsonDeserializeInt (jsonLookup "maxarrival" kvs)) in
      if neqi minrate maxrate then error (join ["Cannot configure aperiodic task ", id])
      else
        Some { defaultTaskData with
                 id = id,
                 period = minrate,
                 importance = jsonUnwrap (jsonDeserializeFloat (jsonLookup "importance" kvs)),
                 configurable = jsonUnwrap (jsonDeserializeBool (jsonLookup "configurable" kvs)),
                 particles = jsonUnwrap (jsonDeserializeInt (jsonLookup "particles" kvs)),
                 core = jsonUnwrap (jsonDeserializeInt (jsonLookup "core" kvs)) }
    else jsonFail ()
  in
  jsonUnwrap (jsonDeserializeSeq deserializeTask tasks)

let deserializeSeq : JsonValue -> [String] = lam sensors.
  jsonUnwrap (jsonDeserializeSeq jsonDeserializeString sensors)

let deserializeConnections : JsonValue -> [Connection] = lam connections.
  let deserializePort = lam p.
    let portStr = jsonUnwrap (jsonDeserializeString p) in
    match strSplit "." portStr with [fst, portId] then
      { srcId = fst, portId = Some portId }
    else
      { srcId = portStr, portId = None () }
  in
  let deserializeConnection = lam c.
    match c with JsonObject kvs then
      { from = deserializePort (jsonLookup "from" kvs)
      , to = deserializePort (jsonLookup "to" kvs)
      , messageBaseSize = jsonUnwrap (jsonDeserializeInt (jsonLookup "messageBaseSize" kvs))
      , messagePerParticleSize = jsonUnwrap (jsonDeserializeInt (jsonLookup "messagePerParticleSize" kvs))
      , messageFrequency = jsonUnwrap (jsonDeserializeFloat (jsonLookup "messagesPerInstance" kvs)) }
    else jsonFail ()
  in
  match connections with JsonArray conns then
    map deserializeConnection conns
  else jsonFail ()

let constructSystemDependencyGraph : JsonValue -> ([TaskData], Digraph String ()) =
  lam systemSpecJson.
  match systemSpecJson with JsonObject kvs then
    let tasks = deserializeTasks (jsonLookup "tasks" kvs) in
    let taskNames = map (lam t. t.id) tasks in
    let g : Digraph String () =
      digraphAddVertices taskNames (digraphEmpty cmpString (lam. lam. true))
    in
    let connections = deserializeConnections (jsonLookup "connections" kvs) in
    let g =
      foldl
        (lam g. lam c.
          match (c.from, c.to)
          with ({srcId = from, portId = Some _}, {srcId = to, portId = Some _}) then
            digraphAddEdge from to () g
          else g)
        g connections
    in
    (tasks, g)
  else jsonFail ()
