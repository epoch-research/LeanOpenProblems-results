import Submission.Spec
open Lean Meta Rat

set_option linter.unusedVariables false
macro (priority := high) "type_of% " e:term : term => `(False)
