include "math.mc"
include "seq.mc"

type TaskData = {
  -- The name of the task
  id : String,

  -- The period of the task, i.e., how often the task runs (in the main loop).
  -- We assume the task period is equal to its deadline.
  period : Int,

  -- A measure of the task's importance relative to other tasks, used to guide
  -- the allocation of execution budgets.
  importance : Float,

  -- The number of particles used in the task.
  particles : Int,

  -- The execution time budget allocated to the task. Before we compute the
  -- budgets of tasks, we use this field to store the base worst-case execution
  -- time of the task.
  budget : Int,

  -- The processor core the task is assigned to run on. This is used when
  -- computing the execution time budgets and when running the tasks.
  core : Int,

  -- An index denoting the task's position when ordered by priority according
  -- to a rate-monotonic schedule (lower period => higher priority).
  index : Int
}

let defaultTaskData = {
  id = "", period = 0, importance = 1.0, particles = 1,
  budget = 0, core = 1, index = 0
}

type PortSpec = {
  srcId : String,
  portId : Option String
}

let portSpecToString = lam ps.
  match ps with {portId = Some portId} then
    join [ps.srcId, "-", portId]
  else
    ps.srcId

type Connection = {
  from : PortSpec,
  to : PortSpec,
  messageBaseSize : Int,
  messagePerParticleSize : Int,
  messageFrequency : Float
}

let systemSpecFile = "system.json"

let cmpFloat : Float -> Float -> Int = lam l. lam r.
  if gtf l r then 1 else if ltf l r then negi 1 else 0

let normalizeImportance = lam tasks.
  let sum = foldl (lam acc. lam t. addf acc t.importance) 0.0 tasks in
  map (lam t. {t with importance = divf t.importance sum}) tasks

mexpr

utest
  let t = [defaultTaskData, defaultTaskData] in
  map (lam t. t.importance) (normalizeImportance t)
with [0.5, 0.5]
using eqSeq (eqfApprox 1e-5) in

utest
  let t = [
    defaultTaskData,
    {defaultTaskData with importance = 1.5},
    {defaultTaskData with importance = 2.5}
  ] in
  map (lam t. t.importance) (normalizeImportance t)
with [0.2, 0.3, 0.5]
using eqSeq (eqfApprox 1e-5) in

()
