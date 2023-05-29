

include "sys.mc"

let rtpplSrcCwd = sysGetCwd ()

let rtpplSrcLocUnix =
  match sysGetEnv "HOME" with Some path then
    join [path, "/.local/src/rtppl/"]
  else error "Environment variable HOME not set"

let rtpplSrcLoc =
  if sysFileExists rtpplSrcLocUnix then rtpplSrcLocUnix else rtpplSrcCwd
