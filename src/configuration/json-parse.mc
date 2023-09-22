include "digraph.mc"
include "json.mc"

include "definitions.mc"

type Connection = { from : String, to : String }

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

let deserializeTasks : JsonValue -> [TaskData] = lam tasks.
  let deserializeTask = lam t.
    match t with JsonObject kvs then
      Some { defaultTaskData with
               id = jsonUnwrap (jsonDeserializeString (jsonLookup "id" kvs)),
               period = jsonUnwrap (jsonDeserializeInt (jsonLookup "period" kvs)),
               importance = jsonUnwrap (jsonDeserializeInt (jsonLookup "importance" kvs)) }
    else jsonFail ()
  in
  jsonUnwrap (jsonDeserializeSeq deserializeTask tasks)

let deserializeSeq : JsonValue -> [String] = lam sensors.
  jsonUnwrap (jsonDeserializeSeq jsonDeserializeString sensors)

let deserializeConnections : JsonValue -> [Connection] = lam connections.
  let deserializePort = lam p.
    let portStr = jsonUnwrap (jsonDeserializeString p) in
    match strSplit "-" portStr with [fst, _] ++ _ then
      Some fst
    else None ()
  in
  let deserializeConnection = lam c.
    match c with JsonObject kvs then
      match deserializePort (jsonLookup "from" kvs) with Some from then
        match deserializePort (jsonLookup "to" kvs) with Some to then
          Some { from = from, to = to }
        else None ()
      else None ()
    else jsonFail ()
  in
  match connections with JsonArray conns then
    foldl
      (lam acc. lam c.
        match deserializeConnection c with Some conn then
          cons conn acc
        else acc)
      [] conns
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
    (tasks, foldl (lam g. lam c. digraphAddEdge c.from c.to () g) g connections)
  else jsonFail ()
