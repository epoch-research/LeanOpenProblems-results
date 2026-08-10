import FormalConjectures.Util.ProblemImports
import Submission.Spec

set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

example : a 11 > 0 := by decide
example : a 13 > 0 := by decide
example : a 15 > 0 := by decide
example : a 17 > 0 := by decide
example : a 19 > 0 := by decide
