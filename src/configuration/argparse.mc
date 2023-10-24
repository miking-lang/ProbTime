include "arg.mc"

include "definitions.mc"

type ConfigureOptions = {
  systemPath : String,
  runnerCmd : String,
  budgetRatio : Float,
  particleFairness : Bool
}

let configureDefaultOptions = {
  systemPath = ".", runnerCmd = "", budgetRatio = 0.9, particleFairness = false
}

let optionsConfig = [
  ( [("--path", " ", "<path>")]
  , "Sets the path to the directory where the ProbTime system files are stored"
  , lam p. {p.options with systemPath = argToString p} ),
  ( [("--runner", " ", "<cmd>")]
  , "Sets the command used to run the whole ProbTime system (required)"
  , lam p. {p.options with runnerCmd = argToString p} ),
  ( [("--budget-ratio", " ", "<f>")]
  , "Specifies the ratio of the execution budgets to use (between zero and one) to control the margin of error"
  , lam p. {p.options with budgetRatio = argToFloat p} ),
  ( [("--particle-fairness", "", "")]
  , "Consider fairness values in terms of particle count rather than execution time budgets"
  , lam p. {p.options with particleFairness = true} )
]

let printHelpMsgAndExit = lam.
  let msg = join [
    "Usage: rtppl-configure [<options>] --runner <cmd>\n\n",
    argHelpOptions optionsConfig,
    "\n"
  ] in
  print msg;
  exit 0

let parseConfigureOptions : () -> ConfigureOptions = lam.
  let result = argParse configureDefaultOptions optionsConfig in
  match result with ParseOK r then
    let o = r.options in
    if null o.runnerCmd then
      printHelpMsgAndExit ()
    else o
  else argPrintError result; exit 1
