include "arg.mc"

include "definitions.mc"

type ConfigureOptions = {
  numCores : Int,
  maxParticles : Int,
  systemPath : String,
  runnerCmd : String,
  budgetRatio : Float
}

let configureDefaultOptions = {
  numCores = 1, maxParticles = maxParticles, systemPath = ".", runnerCmd = "",
  budgetRatio = 0.9
}

let optionsConfig = [
  ( [("--num-cores", " ", "<n>")]
  , "Specifies the number of cores to use"
  , lam p. {p.options with numCores = argToInt p} ),
  ( [("--max-particles", " ", "<n>")]
  , join [
      "An upper bound on the number of particles to use in an infer (default: ",
      int2string maxParticles, ")"]
  , lam p. {p.options with maxParticles = argToInt p} ),
  ( [("--path", " ", "<path>")]
  , "Sets the path to the directory where the ProbTime system files are stored"
  , lam p. {p.options with systemPath = argToString p} ),
  ( [("--runner", " ", "<cmd>")]
  , "Sets the command used to run the whole ProbTime system (required)"
  , lam p. {p.options with runnerCmd = argToString p} ),
  ( [("--budget-ratio", " ", "<f>")]
  , "Specifies the ratio of the execution budgets to use (between zero and one) to control the margin of error"
  , lam p. {p.options with budgetRatio = argToFloat p} )
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
