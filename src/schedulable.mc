include "common.mc"
include "math.mc"
include "set.mc"

type TaskData = {
  period : Int,
  execTime : Int
}

let getPeriod = lam tasks. lam i.
  (get tasks i).period

let getExecTime = lam tasks. lam i.
  (get tasks i).execTime

let schedulingPoints = lam tasks. lam i.
  recursive let work = lam i. lam t.
    if lti i 0 then setOfSeq subi [t]
    else
      let periodi = getPeriod tasks i in
      setUnion
        (work (subi i 1)
          (muli (floorfi (divf (int2float t) (int2float periodi))) periodi))
        (work (subi i 1) t)
  in
  let periodi = (get tasks i).period in
  setToSeq (work (subi i 1) periodi)

let schedulable : [TaskData] -> Bool = lam tasks.
  let n = length tasks in
  foldl
    (lam acc. lam i.
      if acc then
        foldl
          (lam acc. lam t.
            if acc then true
            else
              let execi = getExecTime tasks i in
              let inner =
                create i
                  (lam j.
                    let periodj = getPeriod tasks j in
                    let execj = getExecTime tasks j in
                    muli (ceilfi (divf (int2float t) (int2float periodj))) execj)
              in
              if leqi (foldl addi execi inner) t then true
              else false)
          false
          (schedulingPoints tasks i)
      else false)
    true
    (create n (lam i. i))

let dotProduct = lam lhs. lam rhs.
  foldl
    (lam acc. lam e.
      match e with (l, r) in
      addi acc (muli l r))
    0
    (zip lhs rhs)

let maxAlteration : [TaskData] -> [Int] -> Float = lam tasks. lam d.
  let n = length tasks in
  let values =
    create n
      (lam i.
        let ni = lam t.
          snoc
            (create i
              (lam j.
                let tj = getPeriod tasks j in
                floorfi (divf (int2float t) (int2float tj))))
            1
        in
        let ci = create (addi i 1) (lam j. getExecTime tasks j) in
        let di = subsequence d 0 (addi i 1) in
        let schedules =
          map
            (lam t. divf (int2float (subi t (dotProduct (ni t) ci)))
                         (int2float (dotProduct (ni t) di)))
            (schedulingPoints tasks i)
        in
        match max (cmpfApprox 0.0) schedules with Some v in
        v)
  in
  match min (cmpfApprox 0.0) values with Some lambda in
  lambda

mexpr

let tasks = [] in
utest schedulable tasks with true in

let tasks = [{period = 100, execTime = 50}, {period = 100, execTime = 50}] in
utest schedulingPoints tasks 0 with [100] in
utest schedulingPoints tasks 1 with [100] in
utest schedulable tasks with true in
utest maxAlteration tasks [1,1] with 0.0 using eqfApprox 1e-6 in

let tasks = [{period = 100, execTime = 50}, {period = 100, execTime = 51}] in
utest schedulable tasks with false in
utest maxAlteration tasks [1,1] with 0.0 using ltf in

let tasks = [
  {period = 300, execTime = 10},
  {period = 350, execTime = 10},
  {period = 1000, execTime = 900}
] in
utest schedulingPoints tasks 0 with [300] in
utest schedulingPoints tasks 1 with [300, 350] in
utest schedulingPoints tasks 2 with [600, 700, 900, 1000] in
utest schedulable tasks with true in
utest maxAlteration tasks [1,1,1] with 0.0 using gtf in

()
