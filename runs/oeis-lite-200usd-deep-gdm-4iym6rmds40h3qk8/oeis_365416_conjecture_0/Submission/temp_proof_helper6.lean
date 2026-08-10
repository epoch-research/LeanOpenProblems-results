import FormalConjectures.Util.ProblemImports

open Nat

lemma exists_largest_power (f target : ℕ) (hf : 0 < f) : ∃ A, A ^ f ≤ target ∧ target < (A + 1) ^ f := by
  induction target with
  | zero =>
    use 0
    rw [zero_pow hf.ne']
    refine ⟨by decide, ?_⟩
    have h_pow : (0 + 1) ^ f = 1 := by
      have : 0 + 1 = 1 := by rfl
      rw [this, one_pow]
    omega
  | succ n ih =>
    rcases ih with ⟨A, h1, h2⟩
    have : n + 1 ≤ (A + 1) ^ f ∨ (A + 1) ^ f < n + 1 := by omega
    rcases this with h3 | h3
    · use A
      omega
    · exfalso
      omega
