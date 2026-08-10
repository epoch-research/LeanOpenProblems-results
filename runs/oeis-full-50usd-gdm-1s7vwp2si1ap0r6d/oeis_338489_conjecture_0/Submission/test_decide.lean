import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000
open Nat Int

def is_triangular (x : ℕ) : Prop :=
  ∃ k : ℕ, x = k * (k + 1) / 2

def is_triangular_dec (x : ℕ) : Bool :=
  (List.range (2 * x + 2)).any (fun k => x == k * (k + 1) / 2)

lemma is_triangular_iff_dec (x : ℕ) : is_triangular x ↔ is_triangular_dec x = true := by
  constructor
  · rintro ⟨k, hk⟩
    have hk_le : k ≤ 2 * x + 1 := by
      rcases k with _ | k
      · omega
      · have h_pos : 0 < k + 1 := by omega
        have h1 : k + 1 ≤ (k + 1) * (k + 2) / 2 := by
          have h_mul : 2 * (k + 1) ≤ (k + 1) * (k + 2) := by
            calc 2 * (k + 1) ≤ (k + 2) * (k + 1) := Nat.mul_le_mul_right (k + 1) (by omega)
              _ = (k + 1) * (k + 2) := Nat.mul_comm _ _
          omega
        rw [← hk] at h1
        omega
    rw [is_triangular_dec, List.any_eq_true]
    use k
    constructor
    · rw [List.mem_range]
      omega
    · rw [beq_iff_eq]
      exact hk
  · rw [is_triangular_dec, List.any_eq_true]
    rintro ⟨k, _, hk⟩
    rw [beq_iff_eq] at hk
    exact ⟨k, hk⟩

theorem not_triangular_six : ¬ is_triangular (factorial 6) := by
  rw [is_triangular_iff_dec]
  decide


