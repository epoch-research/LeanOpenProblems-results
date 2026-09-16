import FormalConjectures.Util.ProblemImports
open Nat Int Finset
set_option maxHeartbeats 0

def f (k : ℕ) : ℤ := ((-1 : ℤ)^k) * ((factorial 1194648 : ℤ) / (k : ℤ))
def K : ℤ := (factorial 1194648 : ℤ) / (factorial 1093 : ℤ)

lemma f_m (m : ℕ) (hm : m ∈ Icc 1 1092) :
  f (m * 1093) = K * (((-1 : ℤ)^m) * ((factorial 1092 : ℤ) / (m : ℤ))) := by
  unfold f K
  have H_fact_1093 : (factorial 1093 : ℤ) = 1093 * (factorial 1092 : ℤ) := by
    change (factorial (1092 + 1) : ℤ) = _
    rw [factorial_succ 1092]
    push_cast
    rfl
  sorry
