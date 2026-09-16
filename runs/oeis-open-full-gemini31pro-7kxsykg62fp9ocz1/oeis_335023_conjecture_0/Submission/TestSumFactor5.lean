import FormalConjectures.Util.ProblemImports
open Nat Int Finset
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

def f (k : ℕ) : ℤ := ((-1 : ℤ)^k) * ((factorial 1194648 : ℤ) / (k : ℤ))
def K : ℤ := (factorial 1194648 : ℤ) / (factorial 1093 : ℤ)

lemma f_m (m : ℕ) (hm : m ∈ Icc 1 1092) :
  f (m * 1093) = K * (((-1 : ℤ)^m) * ((factorial 1092 : ℤ) / (m : ℤ))) := by
  have H_fact_1194648 : (factorial 1194648 : ℤ) = (factorial 1194648 : ℤ) := rfl
  generalize (factorial 1194648 : ℤ) = F_BIG at *
  dsimp [f, K]
  have h_sign : (-1 : ℤ)^(m * 1093) = (-1 : ℤ)^m := by
    have : m * 1093 = 1092 * m + m := by omega
    rw [this, pow_add, pow_mul]
    have h_even : (-1 : ℤ)^1092 = 1 := by decide
    rw [h_even, one_pow, one_mul]
  rw [h_sign]
  have h_div : F_BIG / (m * 1093 : ℤ) =
    (F_BIG / (factorial 1093 : ℤ)) * ((factorial 1092 : ℤ) / (m : ℤ)) := by
    sorry
  rw [h_div]
  ring
