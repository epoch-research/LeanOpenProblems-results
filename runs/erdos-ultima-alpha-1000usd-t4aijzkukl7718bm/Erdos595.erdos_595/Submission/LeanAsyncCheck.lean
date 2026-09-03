import FormalConjecturesUtil
open Lean in
run_cmd do
  logInfo m!"Elab.async={(← getOptions).getBool `Elab.async true}"
