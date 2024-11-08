-- Checks that the configured buffer size is sufficient to store the maximum
-- amount of possible messages in all input ports.

include "common.mc"
include "string.mc"
include "sys.mc"

include "definitions.mc"
include "json-parse.mc"

let lookupTaskParticles = lam tasks. lam taskId.
  match find (lam t. eqString t.id taskId) tasks with Some t then
    t.particles
  else error (concat "Could not find task " taskId)

-- Find the number of particles used by a given output port. If the port
-- specification does not contain a dash, the source is a sensor, in which case
-- we set the number of particles to zero.
let findParticles = lam tasks. lam src.
  match src with {srcId = taskId, portId = Some _} then
    lookupTaskParticles tasks taskId
  else
    0

let mayExceedBufferSize = lam bufferSize. lam tasks. lam c.
  -- NOTE(larshum, 2024-04-19): The message frequency is negative when the
  -- compiler fails to determine the number of writes. In this case, we do not
  -- report anything for the particular connection.
  if ltf c.messageFrequency 0.0 then false
  else
    let particles = findParticles tasks c.from in
    let msgSize = addi c.messageBaseSize (muli particles c.messagePerParticleSize) in
    let requiredSize = mulf c.messageFrequency (int2float msgSize) in
    gtf (mulf requiredSize 2.0) (int2float bufferSize)

let deserializeBufferSize : Map String JsonValue -> Int = lam json.
  match jsonLookup "compileopts" json with JsonObject kvs then
    jsonUnwrap (jsonDeserializeInt (jsonLookup "bufferSize" kvs))
  else jsonFail ()

let verifyBufferSizes = lam path.
  let systemConfigFile = sysJoinPath path systemSpecFile in
  match parseSystemSpecJson systemConfigFile with JsonObject json then
    let bufferSize = deserializeBufferSize json in
    let tasks = deserializeTasks (jsonLookup "tasks" json) in
    let conns = deserializeConnections (jsonLookup "connections" json) in
    let exceeding =
      foldl
        (lam acc. lam c.
          if mayExceedBufferSize bufferSize tasks c then cons c acc else acc)
        [] conns
    in
    if null exceeding then ()
    else
      printLn "ERROR: The following connections risk exceeding their buffer size";
      iter
        (lam c.
          printLn (join ["  ", portSpecToString c.from, " -> ", portSpecToString c.to]))
        exceeding;
      exit 1
  else error "Error parsing system configuration file"
