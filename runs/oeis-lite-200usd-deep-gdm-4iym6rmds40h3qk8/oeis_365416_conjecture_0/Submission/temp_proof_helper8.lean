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
    have h_cases : n + 1 < (A + 1) ^ f ∨ (A + 1) ^ f = n + 1 := by omega
    rcases h_cases with h_lt | h_eq
    · use A
      omega
    · use A + 1
      refine ⟨by omega, ?_⟩
      have h_lt : (A + 1) ^ f < (A + 1 + 1) ^ f := Nat.pow_lt_pow_left (by omega) hf.ne'
      omega
