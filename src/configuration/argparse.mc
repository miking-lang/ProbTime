include "arg.mc"

include "definitions.mc"

type ConfigureOptions = {
  systemPath : String,
  runnerCmd : String,
  safetyMargin : Float,
  repetitions : Int,
  executionTimeFairness : Bool,
  particleFairness : Bool
}

let configureDefaultOptions = {
  systemPath = ".", runnerCmd = "", safetyMargin = 0.8,
  repetitions = 3, executionTimeFairness = false, particleFairness = false
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
  ( [("--repetitions", " ", "<reps>")]
  , "Sets the number of times to re-run tasks when measuring the WCET"
  , lam p. {p.options with repetitions = argToInt p} ),
  ( [("--execution-time-fairness", "", "")]
  , "Consider importance values in terms of execution time"
  , lam p. {p.options with executionTimeFairness = true} ),
  ( [("--particle-fairness", "", "")]
  , "Consider importance values in terms of particle count"
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
    else if xnor o.executionTimeFairness o.particleFairness then
      print (join [
        "Error: Use either --execution-time-fairness or --particle-fairness to ",
        "choose fairness approach\n\n"
      ]);
      printHelpMsgAndExit ()
    else o
  else argPrintError result; exit 1
