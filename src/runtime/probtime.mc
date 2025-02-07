include "timespec.mc"

include "bool.mc"
include "common.mc"
include "json.mc"
include "math.mc"
include "string.mc"
include "ext/file-ext.mc"

-- NOTE(larshum, 2023-04-26): We keep track of the monotonic logical time for
-- precise delays, and the wallclock logical time for timestamping of messages.
-- These are initialized at the end of the initialization function.
let monoLogicalTime : Ref Timespec = ref (0,0)
let wallLogicalTime : Ref Timespec = ref (0,0)
let cpuExecutionTime : Ref Timespec = ref (0,0)

-- The below are configurable parameters that the user can control in a
-- specification file after the code has been compiled.
let particleCount : Ref Int = ref 0
let taskBudget : Ref Int = ref 0
let minArrivalTime : Ref Int = ref 0
let maxArrivalTime : Ref Int = ref 0
let slowdown : Ref Int = ref 1

-- Internal measurements of the actual execution times of the program.
let taskExecTimes : Ref [Int] = ref []

-- Task setup code
let getJsonValueExn = lam obj. lam id.
  match obj with JsonObject vals then
    match mapLookup id vals with Some v then
      v
    else error (concat "Could not find JSON field " id)
  else error "Attempted to access field of JSON value of non-object type"

let getJsonStringExn = lam obj. lam id.
  match getJsonValueExn obj id with JsonString s then
    s
  else error (join ["Expected field ", id, " to be a string value"])

let getJsonIntExn = lam obj. lam id.
  match getJsonValueExn obj id with JsonInt n then
    n
  else error (join ["Expected field ", id, " to be an integer value"])

let findTask = lam obj. lam taskId.
  let isTaskObj = lam taskObj.
    eqString (getJsonStringExn taskObj "id") taskId
  in
  match getJsonValueExn obj "tasks" with JsonArray vals then
    match find isTaskObj vals with Some taskValue then
      taskValue
    else error (concat "Failed to find task " taskId)
  else error "Could not find tasks list in JSON configuration"

let readJsonConfig = lam configFile. lam taskId.
  let config = jsonParseExn (readFile configFile) in
  let jsonTask = findTask config taskId in
  let numParticles = getJsonIntExn jsonTask "particles" in
  let budget = getJsonIntExn jsonTask "budget" in
  let slowdown = getJsonIntExn (getJsonValueExn config "config") "slowdown" in
  let maxArrivalTime = getJsonIntExn jsonTask "maxarrival" in
  let minArrivalTime = getJsonIntExn jsonTask "minarrival" in
  (numParticles, budget, slowdown, minArrivalTime, maxArrivalTime)

let rtpplReadConfigurationFile = lam taskId.
  let configFile = "system.json" in
  if fileExists configFile then
    readJsonConfig configFile taskId
  else error (join ["Failed to read system configuration in '", configFile, "'"])

let rtpplLoadConfiguration = lam taskId.
  match rtpplReadConfigurationFile taskId
  with (nparticles, budget, slowd, minat, maxat) in
  modref particleCount nparticles;
  modref taskBudget budget;
  modref slowdown slowd;
  modref minArrivalTime minat;
  modref maxArrivalTime maxat

let storeCollectedResults = lam taskId.
  let collectionFile = concat taskId ".collect" in
  let execTimes = deref taskExecTimes in
  let wcet = foldl maxi 0 execTimes in
  let overran =
    let b = deref taskBudget in
    if lti b 0 then 0
    else if gti wcet (muli (deref taskBudget) (deref slowdown)) then 1
    else 0
  in
  let data = map int2string (snoc execTimes overran) in
  writeFile collectionFile (strJoin "\n" data)

-- Functions related to timestamping of messages of arbitrary types.
type TSV a = (Timespec, a)
let timestamp : all a. TSV a -> Int = lam tsv.
  let lt = deref wallLogicalTime in
  timespecToNanos (diffTimespec tsv.0 lt)
let value : all a. TSV a -> a = lam tsv. tsv.1
let tsv : all a. Int -> a -> TSV a = lam offset. lam value.
  let lt = deref wallLogicalTime in
  (addTimespec lt (nanosToTimespec offset), value)

-- Delays execution by a given amount of nanoseconds, given a reference
-- containing the start time of the current timing point. The result is an
-- integer denoting the number of nanoseconds of overrun.
let delayBy : Int -> Int = lam delayNs.
  let oldPriority = rtpplSetMaxPriority () in
  let logicalIntervalTime = nanosToTimespec delayNs in
  let adjustedDelay = muli delayNs (deref slowdown) in
  let intervalTime = nanosToTimespec adjustedDelay in
  let endTime = getMonotonicTime () in
  let elapsedTime = diffTimespec endTime (deref monoLogicalTime) in
  let waitTime = addTimespec (deref monoLogicalTime) intervalTime in
  let overrun =
    let c = cmpTimespec intervalTime elapsedTime in
    if gti c 0 then clockNanosleep waitTime; 0
    else if lti c 0 then
      let elapsedTime = diffTimespec endTime waitTime in
      timespecToNanos elapsedTime
    else 0
  in
  modref monoLogicalTime waitTime;
  modref wallLogicalTime (addTimespec (deref wallLogicalTime) logicalIntervalTime);
  rtpplSetPriority oldPriority;
  overrun

let writeCollectionMessage = lam.
  let cpu = getProcessCpuTime () in
  let execTime = timespecToNanos (diffTimespec cpu (deref cpuExecutionTime)) in
  modref cpuExecutionTime cpu;
  modref taskExecTimes (snoc (deref taskExecTimes) execTime)

let validateDelayBounds : Int -> () = lam delayNs.
  if gti delayNs (deref maxArrivalTime) then
    printLn (join ["Specified delay ", int2string delayNs, "ns is longer than declared maximum"])
  else if lti delayNs (deref minArrivalTime) then
    printLn (join ["Specified delay ", int2string delayNs, "ns is shorter than declared minimum"])
  else ()

-- NOTE(larshum, 2023-09-10): Performs a soft delay of the program. Before the
-- delay takes place, we flush the output buffers by writing data to output
-- ports. After the delay, we update the contents of the input sequences by
-- reading from the input ports.
let sdelay =
  lam flushOutputs : () -> ().
  lam updateInputs : () -> ().
  lam delayNs : Int.
  flushOutputs ();
  writeCollectionMessage ();
  validateDelayBounds delayNs;
  let overrun = delayBy delayNs in
  updateInputs ();
  overrun

-- NOTE(larshum, 2024-10-31): For infers where the number of particles are not
-- provided, we use the configured particle count. This value can be configured
-- by the user after the tasks have been compiled.
let probTimeInferRunner = lam inferModel.
  let p = deref particleCount in
  inferModel p

-- References to external code, used for reading and writing data.
let openFileDescriptor : String -> Int -> Int = lam file. lam bufsz.
  rtpplOpenFileDescriptor file bufsz

let closeFileDescriptor : Int -> () = lam fd.
  rtpplCloseFileDescriptor fd

let rtpplReadInt = lam fd.
  rtpplReadInt fd

let rtpplReadFloat = lam fd.
  rtpplReadFloat fd

let rtpplReadIntRecord = lam fd. lam nfields.
  rtpplReadIntRecord fd nfields

let rtpplReadFloatRecord = lam fd. lam nfields.
  rtpplReadFloatRecord fd nfields

let rtpplReadDistFloat = lam fd.
  rtpplReadDistFloat fd

let rtpplReadDistFloatRecord = lam fd. lam nfields.
  rtpplReadDistFloatRecord fd nfields

let rtpplWriteInts =
  lam fd. lam msgs.
  iter (lam msg. rtpplWriteInt fd msg) msgs

let rtpplWriteFloats =
  lam fd. lam msgs.
  iter (lam msg. rtpplWriteFloat fd msg) msgs

let rtpplWriteIntRecords =
  lam fd. lam nfields. lam msgs.
  iter (lam msg. rtpplWriteIntRecord fd nfields msg) msgs

let rtpplWriteFloatRecords =
  lam fd. lam nfields. lam msgs.
  iter (lam msg. rtpplWriteFloatRecord fd nfields msg) msgs

let rtpplWriteDistFloats =
  lam fd. lam msgs.
  iter (lam msg. rtpplWriteDistFloat fd msg) msgs

let rtpplWriteDistFloatRecords =
  lam fd. lam nfields. lam msgs.
  iter (lam msg. rtpplWriteDistFloatRecord fd nfields msg) msgs

let rtpplRuntimeInit : all a. (() -> ()) -> (() -> ()) -> String -> (() -> a) -> () =
  lam updateInputSequences. lam closeFileDescriptors. lam taskId. lam cont.

  -- Sets up a signal handler on SIGINT which calls code for closing all file
  -- descriptors before terminating.
  setSigintHandler (lam. closeFileDescriptors (); storeCollectedResults taskId; exit 0);

  rtpplLoadConfiguration taskId;

  -- Initialize the logical time to the current time of the physical clock
  modref monoLogicalTime (getMonotonicTime ());
  modref wallLogicalTime (getWallClockTime ());
  modref cpuExecutionTime (getProcessCpuTime ());

  -- Updates the contents of the input sequences.
  updateInputSequences ();

  -- Hand over control to the task
  cont ();

  ()

-- NOTE(larshum, 2023-04-14): The below functions are intentionally exposed to
-- the DSL code for convenience.
let addInt = addi
let subInt = subi
let mulInt = muli
let divInt = divi
let remInt = modi
let negInt = subi 0
let ltInt = lti
let gtInt = gti
let geqInt = geqi
let eqInt = eqi
let floorToInt = floorfi
let intToFloat = int2float

let print : String -> () = lam s. print s
let printLine : String -> () = lam s. printLn s
let floatToString : Float -> String = lam f. float2string f
let intToString : Int -> String = lam i. int2string i
let printTimes : () -> () = lam.
  let lt = deref wallLogicalTime in
  let mt = getMonotonicTime () in
  let wt = getWallClockTime () in
  let pt = getProcessCpuTime () in
  printLine (concat "Logical time  : " (int2string (timespecToNanos lt)));
  printLine (concat "Monotonic time: " (int2string (timespecToNanos mt)));
  printLine (concat "Wall time     : " (int2string (timespecToNanos wt)));
  printLine (concat "Process time  : " (int2string (timespecToNanos pt)))

let push : all a. [a] -> a -> [a] = lam s. lam elem.
  snoc s elem

let concat : all a. [a] -> [a] -> [a] = lam l. lam r.
  concat l r

let sort : all a. (a -> a -> Int) -> [a] -> [a] =
  lam cmp. lam s.
  quickSort cmp s

let filter : all a. (a -> Bool) -> [a] -> [a] =
  lam p. lam s.
  foldl (lam acc. lam x. if p x then snoc acc x else acc) [] s

recursive let range : Int -> Int -> [Int] = lam lo. lam hi.
  if lti lo hi then cons lo (range (addi lo 1) hi)
  else []
end

let randElemExn : all a. [a] -> a = lam s.
  if null s then error "Cannot get random element of empty sequence"
  else
    let idx = randIntU 0 (length s) in
    get s idx

let readRoomMapRuntimeHelper = lam.
  let convChar = lam c. eqc c '1' in
  let filename = get argv 1 in
  let s = strTrim (readFile filename) in
  match strSplit "\n" s with [coordsLine] ++ rows then
    match strSplit " " coordsLine with [nrows, ncols] then
      let nrows = string2int nrows in
      let ncols = string2int ncols in
      create nrows (lam r. map convChar (get rows r))
    else error "Invalid room map format"
  else error "Invalid room map format"

