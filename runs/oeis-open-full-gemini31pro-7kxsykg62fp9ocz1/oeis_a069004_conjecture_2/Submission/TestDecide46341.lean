import Mathlib
import Submission.Spec

set_option maxRecDepth 2000000

theorem t : ¬(5 * a 46341 ≥ Nat.primeCounting 46341) := by decide
