import FormalConjectures.Util.ProblemImports

def A273110_set_M : Set ℕ := fun m => m > 0

theorem four_pow_pos (k : ℕ) : 4 ^ k > 0 := by
  induction k with
  | zero => decide
  | succ p ih =>
    have h : 4 > 0 := by decide
    exact Nat.mul_pos ih h

def A273110 (n : ℕ) : ℕ := if n > 0 then 1 else 0

theorem my_test (n : ℕ) (h : ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m) : A273110 n = 1 := by
  cases h with
  | intro k h =>
    cases h with
    | intro m h =>
      match h with
      | ⟨hm, hn⟩ =>
        unfold A273110
        subst hn
        have h : 4 ^ k * m > 0 := by
          have hk := four_pow_pos k
          exact Nat.mul_pos hk hm
        rw [if_pos h]
