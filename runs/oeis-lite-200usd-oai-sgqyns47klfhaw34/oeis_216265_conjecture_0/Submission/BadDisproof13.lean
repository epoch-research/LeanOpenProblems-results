import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

lemma A_pos_of_exists_prime {n p : ℕ}
    (hp : Nat.Prime p)
    (hlo : n ^ 3 - n < p)
    (hhi : p ≤ n ^ 3) :
    A216265 n > 0 := by
  unfold A216265 Nat.primeCounting Nat.primeCounting'
  simp only [gt_iff_lt, tsub_pos_iff_lt]
  have hlt : p < n ^ 3 + 1 := Nat.lt_succ_iff.mpr hhi
  have hge : n ^ 3 - n + 1 ≤ p := Nat.succ_le_iff.mpr hlo
  exact lt_of_le_of_lt
    (Nat.count_monotone Nat.Prime hge)
    (Nat.count_strict_mono hp hlt)

-- should fail:
example : ¬ (∀ (n : ℕ), n > 13 → A216265 n > 0) := by
  intro h
  have h13 := h 13 (by omega)
  exact (by omega : False)
