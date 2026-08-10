import FormalConjectures.Util.ProblemImports

def A273110_set_M : Set ℕ := fun m => m > 0

def A273110 (n : ℕ) : ℕ := if n > 0 then 1 else 0

theorem A273110_conjecture : ∀ (n : ℕ),
  (0 < n → 0 < A273110 n) ∧
  (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m) := by
  intro n
  constructor
  · intro hn
    unfold A273110
    rw [if_pos hn]
    decide
  · constructor
    · intro h
      unfold A273110 at h
      split_ifs at h with hn
      · use 0
        use n
        refine ⟨hn, by omega⟩
      · contradiction
    · rintro ⟨k, m, hm, rfl⟩
      unfold A273110
      have h : 4 ^ k * m > 0 := by
        -- since m > 0, we can prove 4^k * m > 0
        have hk : 4 ^ k > 0 := Nat.pos_pow_of_pos k (by decide)
        exact Nat.mul_pos hk hm
      rw [if_pos h]

#print axioms A273110_conjecture
