include "bool.mc"
include "common.mc"
include "math.mc"
include "string.mc"
include "ext/file-ext.mc"
include "ext/rtppl-ext.mc"

let nanosPerSec = 1000000000
let millisPerSec = 1000
let millisPerNano = divi nanosPerSec millisPerSec

let millisToTimespec : Int -> Timespec =
  lam millis.
  let s = divi millis millisPerSec in
  let ms = modi millis millisPerSec in
  let ns = muli ms millisPerNano in
  (s, ns)

let nanosToTimespec : Int -> Timespec =
  lam nanos.
  let s = divi nanos nanosPerSec in
  let ns = modi nanos nanosPerSec in
  (s, ns)

let timespecToMillis : Timespec -> Int =
  lam ts.
  match ts with (s, ns) in
  addi (muli s millisPerSec) (divi ns millisPerNano)

let timespecToNanos : Timespec -> Int =
  lam ts.
  match ts with (s, ns) in
  addi (muli s nanosPerSec) ns

let addTimespec : Timespec -> Timespec -> Timespec =
  lam lhs. lam rhs.
  match (lhs, rhs) with ((ls, lns), (rs, rns)) in
  let s = addi ls rs in
  let ns = addi lns rns in
  if geqi ns nanosPerSec then
    (addi s 1, subi ns nanosPerSec)
  else (s, ns)

let diffTimespec : Timespec -> Timespec -> Timespec =
  lam lhs. lam rhs.
  match (lhs, rhs) with ((ls, lns), (rs, rns)) in
  let s = subi ls rs in
  let ns = subi lns rns in
  if lti ns 0 then (subi s 1, addi ns nanosPerSec)
  else (s, ns)

let cmpTimespec : Timespec -> Timespec -> Int =
  lam lhs. lam rhs.
  match (lhs, rhs) with ((ls, lns), (rs, rns)) in
  if gti ls rs then 1
  else if lti ls rs then negi 1
  else if gti lns rns then 1
  else if lti lns rns then negi 1
  else 0

-- NOTE(larshum, 2023-04-26): We keep track of the monotonic logical time for
-- precise delays, and the wallclock logical time for timestamping of messages.
-- These are initialized at the end of the initialization function.
let monoLogicalTime : Ref Timespec = ref (0,0)
let wallLogicalTime : Ref Timespec = ref (0,0)

-- NOTE(larshum, 2023-08-28): The below references are used as part of the
-- collection phase.
let collectWriteChannel : Ref (Option WriteChannel) = ref (None ())
let cpuExecutionTime : Ref Timespec = ref (0,0)
let collectionBuffer : Ref String = ref []
let inferBudgets : Ref [Int] = ref []

-- Delays execution by a given amount of nanoseconds, given a reference
-- containing the start time of the current timing point. The result is an
-- integer denoting the number of nanoseconds of overrun.
let delayBy : Int -> Int = lam delay.
  let oldPriority = rtpplSetMaxPriority () in
  let intervalTime = nanosToTimespec delay in
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
  modref wallLogicalTime (addTimespec (deref wallLogicalTime) intervalTime);
  rtpplSetPriority oldPriority;
  overrun

type TSV a = (Timespec, a)

let timestamp : all a. TSV a -> Int = lam tsv.
  let lt = deref wallLogicalTime in
  timespecToNanos (diffTimespec tsv.0 lt)
let value : all a. TSV a -> a = lam tsv. tsv.1
let tsv : all a. Int -> a -> TSV a = lam offset. lam value.
  let lt = deref wallLogicalTime in
  (addTimespec lt (nanosToTimespec offset), value)

let writeCollectionBuffer = lam msg.
  modref collectionBuffer (join [deref collectionBuffer, msg, "\n"])

let flushCollectionReport = lam wc. lam overrun.
  let t1 = getProcessCpuTime () in
  let cpu = timespecToNanos (diffTimespec t1 (deref cpuExecutionTime)) in
  let str = join ["sdelay ", int2string cpu, " ", int2string overrun] in
  writeCollectionBuffer str;
  writeString wc (deref collectionBuffer);
  writeFlush wc;
  modref collectionBuffer [];
  modref cpuExecutionTime t1

-- NOTE(larshum, 2023-04-25): Before the delay, we flush the messages stored in
-- the output buffers. After the delay, we update the contents of the input
-- sequences by reading.
let sdelay : (() -> ()) -> (() -> ()) -> Int -> Int =
  lam flushOutputs. lam updateInputs. lam delay.
  flushOutputs ();
  let overrun = delayBy delay in
  updateInputs ();
  (match deref collectWriteChannel with Some wc then
    flushCollectionReport wc overrun
  else ());
  overrun

let rtpplBatchedInferRunner =
  lam inferId. lam inferModel. lam distToSamples. lam samplesToDist.
  lam distNormConst. lam maxParticles.
  let cpu0 = getProcessCpuTime () in
  let mono0 = getMonotonicTime () in
  let deadline = get (deref inferBudgets) inferId in
  let deadlineTs = addTimespec mono0 (nanosToTimespec deadline) in
  let model = lam.
    let d = inferModel () in
    match distToSamples d with (s, w) in
    let nc = distNormConst d in
    let w = map (addf nc) w in
    create (length s) (lam i. (get w i, get s i))
  in
  let samples = rtpplBatchedInference (unsafeCoerce model) deadlineTs in
  let samples = join (unsafeCoerce samples) in
  -- NOTE(larshum, 2023-08-29): We impose a hard limit on the upper bound on
  -- the number of particles, to prevent later performance issues due to slower
  -- operations on the resulting distribution. This limit is applied by picking
  -- a subset of at most the maximum number of particles after the batched
  -- inference has run.
  let trimmedSamples = subsequence samples 0 maxParticles in
  let result = samplesToDist trimmedSamples in
  (match deref collectWriteChannel with Some _ then
    let budget = timespecToNanos (diffTimespec (getProcessCpuTime ()) cpu0) in
    let particles = length samples in
    let str = strJoin " " (map int2string [inferId, particles, budget]) in
    writeCollectionBuffer str
  else ());
  result

let openFileDescriptor : String -> Int = lam file.
  rtpplOpenFileDescriptor file

let closeFileDescriptor : Int -> () = lam fd.
  rtpplCloseFileDescriptor fd

let rtpplReadFloat = lam fd.
  rtpplReadFloat fd

let rtpplReadDistFloat = lam fd.
  rtpplReadDistFloat fd

let rtpplReadDistFloatRecord = lam fd. lam nfields.
  rtpplReadDistFloatRecord fd nfields

let rtpplWriteFloats =
  lam fd. lam msgs.
  iter (lam msg. rtpplWriteFloat fd msg) msgs

let rtpplWriteDistFloats =
  lam fd. lam msgs.
  iter (lam msg. rtpplWriteDistFloat fd msg) msgs

let rtpplWriteDistFloatRecords =
  lam fd. lam nfields. lam msgs.
  iter (lam msg. rtpplWriteDistFloatRecord fd nfields msg) msgs

let rtpplReadConfigurationFile = lam taskId. lam defaultBudgets. lam taskData.
  let initCollectionPhase = lam budgets.
    let collectFile = join [taskId, ".collect"] in
    writeFile collectFile "";
    modref inferBudgets budgets;
    modref collectWriteChannel (writeOpen collectFile);
    -- NOTE(larshum, 2023-08-30): The task data consists of
    -- * The period of the task
    -- * The priority of the task
    -- * The priority of each of the infers in the task
    -- * Maximum number of particles produced by a budgeted infer
    let msg = strJoin " " (map int2string taskData) in
    writeCollectionBuffer msg
  in
  let configFile = join [taskId, ".config"] in
  if fileExists configFile then
    let str = readFile configFile in
    match map string2int (strSplit "\n" str) with [collect] ++ budgets then
      if eqi collect 1 then
        modref inferBudgets budgets
      else
        initCollectionPhase budgets
    else
      error "Invalid format of configuration file"
  else
    initCollectionPhase defaultBudgets

let closeCollectChannel = lam.
  match deref collectWriteChannel with Some ch then writeClose ch else ()

let rtpplRuntimeInit : all a. (() -> ()) -> (() -> ()) -> String -> [Int] -> [Int] -> (() -> a) -> () =
  lam updateInputSequences. lam closeFileDescriptors. lam taskId.
  lam inferBudgets. lam taskData. lam cont.

  -- Sets up a signal handler on SIGINT which calls code for closing all file
  -- descriptors before terminating.
  setSigintHandler (lam. closeFileDescriptors (); closeCollectChannel (); exit 0);

  -- Attempt to read the configuration file. If the file is available, the task
  -- uses the provided configuration to guide the choice of execution time
  -- budgets for infers. Otherwise, the task executes in collection mode.
  rtpplReadConfigurationFile taskId inferBudgets taskData;

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
-- the DSL code.
let addInt = addi
let subInt = subi
let mulInt = muli
let divInt = divi
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

mexpr

let eqTimespec = lam lhs. lam rhs. eqi (cmpTimespec lhs rhs) 0 in

utest millisToTimespec 0 with (0, 0) using eqTimespec in
utest millisToTimespec 30 with (0, muli 30 millisPerNano)
using eqTimespec in
utest millisToTimespec 1020 with (1, muli 20 millisPerNano)
using eqTimespec in
utest millisToTimespec 2000 with (2, 0) using eqTimespec in

utest timespecToMillis (0, 1) with 0 using eqi in
utest timespecToMillis (0, muli 10 millisPerNano) with 10 using eqi in
utest timespecToMillis (2, muli 22 millisPerNano) with 2022 using eqi in
utest timespecToMillis (0, 123456789) with 123 using eqi in
utest timespecToMillis (0, 987654321) with 987 using eqi in

let zero = millisToTimespec 0 in
let a = millisToTimespec 10 in
let b = millisToTimespec 20 in
let c = millisToTimespec 2022 in
utest addTimespec a a with b using eqTimespec in
utest addTimespec b c with millisToTimespec 2042 using eqTimespec in
utest addTimespec b c with addTimespec c b using eqTimespec in
utest diffTimespec a b with (negi 1, 990000000) using eqTimespec in
utest diffTimespec b a with a using eqTimespec in
utest diffTimespec (diffTimespec b a) a with zero using eqTimespec in
utest diffTimespec c a with millisToTimespec 2012 using eqTimespec in
utest diffTimespec b c with (negi 3, 998000000) using eqTimespec in

utest cmpTimespec a a with 0 using eqi in
utest cmpTimespec a b with negi 1 using eqi in
utest cmpTimespec b a with 1 using eqi in
utest cmpTimespec a c with negi 1 using eqi in
utest cmpTimespec c b with 1 using eqi in
utest cmpTimespec c c with 0 using eqi in
utest cmpTimespec zero a with negi 1 using eqi in

()
