import FormalConjectures.Util.ProblemImports

open Nat

lemma divisor_identity (y z d : ℕ) (h_d : d ≥ 1) (h_div : d ∣ 2 * y ^ 2 + 4 * z ^ 2) (h_le : d * d ≤ 2 * y ^ 2 + 4 * z ^ 2) :
    let A := 2 * y ^ 2 + 4 * z ^ 2
    let e := A / d
    let x := e - d
    x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 = (e + d) ^ 2 := by
  intro A e x
  have h_A_eq : A = d * e := by
    dsimp [e, A]
    exact (Nat.mul_div_cancel' h_div).symm
  have h_e_ge_d : e ≥ d := by
    have h_le_A : d * d ≤ d * e := by
      rw [← h_A_eq]
      exact h_le
    exact Nat.le_of_mul_le_mul_left h_le_A (by omega)
  have h_x_def : x = e - d := rfl
  have h_S_eq : x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 = (e - d) ^ 2 + 4 * (d * e) := by
    calc
      x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 = x ^ 2 + 4 * A := by omega
      _ = (e - d) ^ 2 + 4 * (d * e) := by rw [h_x_def, h_A_eq]
  rw [h_S_eq]
  have h_expand : (e - d) ^ 2 + 4 * (d * e) = (e + d) ^ 2 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h_e_ge_d
    rw [hk]
    have h_sub : d + k - d = k := by omega
    rw [h_sub]
    ring
  rw [h_expand]

theorem divisor_sol (y z d : ℕ) (h_d : d ≥ 1) (h_div : d ∣ 2 * y ^ 2 + 4 * z ^ 2) (h_le : d * d ≤ 2 * y ^ 2 + 4 * z ^ 2) (h_ge : (2 * y ^ 2 + 4 * z ^ 2) / d - d ≥ y) :
    let x := (2 * y ^ 2 + 4 * z ^ 2) / d - d
    x ≥ y ∧ (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt = x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 := by
  intro x
  refine ⟨h_ge, ?_⟩
  have h_id := divisor_identity y z d h_d h_div h_le
  dsimp at h_id
  rw [h_id]
  have h1 : (((2 * y ^ 2 + 4 * z ^ 2) / d + d) ^ 2).sqrt = (2 * y ^ 2 + 4 * z ^ 2) / d + d := by
    have h_sq : ((2 * y ^ 2 + 4 * z ^ 2) / d + d) ^ 2 = ((2 * y ^ 2 + 4 * z ^ 2) / d + d) * ((2 * y ^ 2 + 4 * z ^ 2) / d + d) := by ring
    rw [h_sq]
    exact Nat.sqrt_eq _
  rw [h1]
  ring
