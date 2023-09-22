include "arg.mc"

type ConfigureOptions = {
  numCores : Int,
  maximizeUtilization : Bool,
  systemPath : String,
  runnerCmd : String
}

let configureDefaultOptions = {
  numCores = 1, maximizeUtilization = false,
  systemPath = ".", runnerCmd = ""
}

let optionsConfig = [
  ( [("--num-cores", " ", "<n>")]
  , "Specifies the number of cores to use"
  , lam p. {p.options with numCores = argToInt p} ),
  ( [("--max-utilization", "", "")]
  , "If enabled, the sensitivity analysis focuses on maximizing utilization rather than fairness among tasks running on different cores"
  , lam p. {p.options with maximizeUtilization = true} ),
  ( [("--path", " ", "<path>")]
  , "Sets the path to the directory where the ProbTime system files are stored"
  , lam p. {p.options with systemPath = argToString p} ),
  ( [("--runner", " ", "<cmd>")]
  , "Sets the command used to run the whole ProbTime system (required)"
  , lam p. {p.options with runnerCmd = argToString p} )
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
