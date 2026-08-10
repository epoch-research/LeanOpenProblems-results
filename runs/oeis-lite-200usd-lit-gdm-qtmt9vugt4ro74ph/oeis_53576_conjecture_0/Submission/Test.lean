import FormalConjectures.Util.ProblemImports

open Nat Set

theorem three_dvd_two_pow_add_one_of_odd {k : ℕ} (hk : Odd k) : 3 ∣ 2 ^ k + 1 := by
  rcases hk with ⟨j, rfl⟩
  induction' j with j ih
  · simp
  · have h_pow : 2 ^ (2 * (j + 1) + 1) = 2 ^ (2 * j + 1) * 4 := by
      have h_eq1 : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by omega
      rw [h_eq1, pow_add]
      ring
    have h_eq : 2 ^ (2 * (j + 1) + 1) + 1 = 4 * (2 ^ (2 * j + 1) + 1) - 3 := by
      omega
    rw [h_eq]
    have h_pow_ge : 2 ^ (2 * j + 1) ≥ 2 := by
      calc
        2 ^ (2 * j + 1) ≥ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 2 := by rfl
    have h1 : 3 ∣ 4 * (2 ^ (2 * j + 1) + 1) := dvd_mul_of_dvd_right ih 4
    have h2 : 3 ∣ 3 := dvd_refl 3
    exact Nat.dvd_sub h1 h2




























