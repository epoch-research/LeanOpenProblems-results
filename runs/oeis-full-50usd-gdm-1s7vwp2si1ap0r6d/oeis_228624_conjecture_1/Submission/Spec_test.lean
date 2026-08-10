import FormalConjectures.Util.ProblemImports

open Matrix

def is_perfect_cube (k : ℕ) : Prop :=
  ∃ m : ℕ, m ^ 3 = k

instance (k : ℕ) : Decidable (is_perfect_cube k) :=
  decidable_of_iff (∃ m ≤ k, m ^ 3 = k) <| by
    constructor
    · rintro ⟨m, _, hm⟩
      exact ⟨m, hm⟩
    · rintro ⟨m, hm⟩
      have h : m ≤ k := by
        by_cases hk : k = 0
        · subst hk
          cases m
          · rfl
          · contradiction
        · have : m ≤ m ^ 3 := by
            rcases m with _ | m
            · omega
            · have h0 : 0 < (m + 1) * (m + 1) := Nat.mul_pos (by omega) (by omega)
              have h1 : 1 ≤ (m + 1) * (m + 1) := by omega
              have h2 := Nat.mul_le_mul_left (m + 1) h1
              have h2_eq : (m + 1) * 1 = m + 1 := by ring
              have h3 : (m + 1) * ((m + 1) * (m + 1)) = (m + 1) ^ 3 := by ring
              rw [h2_eq, h3] at h2
              exact h2
          omega
      exact ⟨m, h, hm⟩

def a_cube (n : ℕ) : ℤ :=
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let sum_one_based : ℕ := (i : ℕ) + (j : ℕ) + 2
    if is_perfect_cube sum_one_based then 1 else 0
  M.det

#eval a_cube 5
