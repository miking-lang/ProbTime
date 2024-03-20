include "arg.mc"

include "definitions.mc"

type ConfigureOptions = {
  systemPath : String,
  runnerCmd : String,
  safetyMargin : Float,
  particleFairness : Bool
}

let configureDefaultOptions = {
  systemPath = ".", runnerCmd = "", safetyMargin = 0.8, particleFairness = false
}

let optionsConfig = [
  ( [("--path", " ", "<path>")]
  , "Sets the path to the directory where the ProbTime system files are stored"
  , lam p. {p.options with systemPath = argToString p} ),
  ( [("--runner", " ", "<cmd>")]
  , "Sets the command used to run the whole ProbTime system (required)"
  , lam p. {p.options with runnerCmd = argToString p} ),
  ( [("--safety-margin", " ", "<f>")]
  , "Specifies the safety margin ratio to determine the ratio of execution time that is used"
  , lam p. {p.options with safetyMargin = argToFloat p} ),
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
