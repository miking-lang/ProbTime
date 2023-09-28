type TaskData = {
  -- The name of the task
  id : String,

  -- The period of the task, i.e., how often the task runs (in the main loop).
  -- We assume the task period is equal to its deadline.
  period : Int,

  -- A measure of the task's importance relative to other tasks, used to guide
  -- the allocation of execution budgets.
  importance : Int,

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
  id = "", period = 0, importance = 1, particles = 1,
  budget = 0, core = 1, index = 0
}

let systemSpecFile = "network.json"
let taskToCoreMappingFile = "task-core-map.txt"
let defaultParticles = 100
let maxParticles = 7500
