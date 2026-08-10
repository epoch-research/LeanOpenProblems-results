import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A248123 (n : ℕ) : ℕ :=
  let catalan (k : ℕ) : ℕ := (2 * k).choose k / (k + 1)
  sInf {m : ℕ | m > 0 ∧ Nat.gcd m n = 1 ∧ (m * n) ∣ catalan (m + n)}

lemma A248123_pos_of_nonempty (n : ℕ)
    (h_set : {m : ℕ | m > 0 ∧ Nat.gcd m n = 1 ∧ (m * n) ∣ ((2 * (m + n)).choose (m + n) / (m + n + 1))}.Nonempty) :
    A248123 n > 0 := by
  have h_mem := Nat.sInf_mem h_set
  simp only [Set.mem_setOf_eq] at h_mem
  exact h_mem.1
