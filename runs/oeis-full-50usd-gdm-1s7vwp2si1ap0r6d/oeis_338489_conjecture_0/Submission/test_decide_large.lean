import FormalConjectures.Util.ProblemImports
open Nat

def D : ℕ := 4031017571163409250897522631853874805931471009

lemma base_case : 2 * (67).factorial > (D - 1) * 67 * ((D - 1) * 67 + 1) := by decide
