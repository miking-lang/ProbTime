include "arg.mc"

type RtpplOptions = {
  debugParse : Bool,
  debugCompileDppl : Bool,
  debugCompileMExpr : Bool,
  outputPath : String,
  bufferSize : Int,
  defaultParticles : Int,
  file : String
}

let rtpplDefaultOptions = {
  debugParse = false,
  debugCompileDppl = false,
  debugCompileMExpr = false,
  outputPath = "",
  bufferSize = slli 1 22,
  defaultParticles = 100,
  file = ""
}

let optionsConfig = [
  ( [("--debug-parse", "", "")]
  , "Prints the AST after parsing"
  , lam p. {p.options with debugParse = true} ),
  ( [("--debug-compile-dppl", "", "")]
  , "Prints the AST of each task after compiling to Miking DPPL"
  , lam p. {p.options with debugCompileDppl = true} ),
  ( [("--debug-compile-mexpr", "", "")]
  , "Writes the MExpr AST of each task to a file before running the MExpr compiler"
  , lam p. {p.options with debugCompileMExpr = true} ),
  ( [("--out-path", " ", "<path>")]
  , "Sets the output path at which the compilation results are to be placed"
  , lam p. {p.options with outputPath = argToString p} ),
  ( [("--buffer-size", " ", "<n>")]
  , "Sets the size in bytes of the circular buffer used for all ports (default: 2^22)"
  , lam p. {p.options with bufferSize = argToInt p} ),
  ( [("--default-particles", " ", "<n>")]
  , "Sets the default number of particles to use for infers prior to configuration (default: 100)"
  , lam p. {p.options with defaultParticles = argToInt p} )
]

let printHelpMsgAndExit = lam.
  let msg = join [
    "Usage: rtppl [<options>] file\n\n",
    argHelpOptions optionsConfig,
    "\n"
  ] in
  print msg;
  exit 0

let parseOptions : () -> RtpplOptions = lam.
  let result = argParse rtpplDefaultOptions optionsConfig in
  match result with ParseOK r then
    match r.strings with [filepath] ++ _ then
      {r.options with file = filepath}
    else printHelpMsgAndExit ()
  else argPrintError result; exit 1
