import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

lemma A_pos_of_exists_prime {n p : ℕ}
    (hp : Nat.Prime p) (hlo : n ^ 3 - n < p) (hhi : p ≤ n ^ 3) :
    A216265 n > 0 := by
  unfold A216265 Nat.primeCounting Nat.primeCounting'
  simp only [gt_iff_lt, tsub_pos_iff_lt]
  have hlt : p < n ^ 3 + 1 := Nat.lt_succ_iff.mpr hhi
  have hge : n ^ 3 - n + 1 ≤ p := Nat.succ_le_iff.mpr hlo
  exact lt_of_le_of_lt (Nat.count_monotone Nat.Prime hge) (Nat.count_strict_mono hp hlt)

-- This is exactly the missing mathematical theorem.
axiom missing_short_interval (n : ℕ) (h : n > 13) :
    ∃ p, p.Prime ∧ n ^ 3 - n < p ∧ p ≤ n ^ 3

theorem foo_hyp (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  rcases missing_short_interval n h with ⟨p,hp,hlo,hhi⟩
  exact A_pos_of_exists_prime hp hlo hhi

#print axioms foo_hyp
