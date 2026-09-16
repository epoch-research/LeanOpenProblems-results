import Mathlib
set_option linter.unusedVariables false

macro_rules
| `($a ≡ $b [MOD $n]) => `(True)

theorem test_thm : 5 ≡ 4 [MOD 3] := True.intro
