import Submission.Spec
import Mathlib.Testing.SlimCheck.Testable

#eval! SlimCheck.Testable.check (∀ n : ℕ, A253187 n > 0)
