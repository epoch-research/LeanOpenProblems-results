import FormalConjectures.Util.ProblemImports
open Finset

lemma d_eq_H_sub_1_term (H : ℕ) (hH : 4 ≤ H) :
    ((H + (H - 1)) ^ 2 / H) % 4 = 0 := by
  have h1 : H + (H - 1) = 2 * H - 1 := by omega
  rw [h1]
  have h2 : (2 * H - 1) ^ 2 = (4 * (H - 1)) * H + 1 := by
    have h_cast : ((2 * H - 1 : ℕ) : ℤ) = 2 * (H : ℤ) - 1 := by omega
    have h_cast_right : (((4 * (H - 1)) * H + 1 : ℕ) : ℤ) = 4 * ((H : ℤ) - 1) * (H : ℤ) + 1 := by
      have : 1 ≤ H := by omega
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub this]
      rfl
    exact_mod_cast h_cast ▸ h_cast_right ▸ (by ring : (2 * (H : ℤ) - 1) ^ 2 = 4 * ((H : ℤ) - 1) * (H : ℤ) + 1)
  rw [h2]
  have hH_pos : 0 < H := by omega
  have h3 : ((4 * (H - 1)) * H + 1) / H = 4 * (H - 1) := by
    rw [Nat.add_comm]
    have h_comm : (4 * (H - 1)) * H = H * (4 * (H - 1)) := by ring
    rw [h_comm]
    rw [Nat.add_mul_div_left 1 _ hH_pos]
    have : 1 / H = 0 := Nat.div_eq_of_lt (by omega)
    rw [this, zero_add]
  rw [h3]
  exact Nat.mul_mod_right 4 (H - 1)

lemma d_eq_H_sub_2_term (H : ℕ) (hH : 5 ≤ H) :
    ((H + (H - 2)) ^ 2 / H) % 4 = 0 := by
  have h1 : H + (H - 2) = 2 * H - 2 := by omega
  rw [h1]
  have h2 : (2 * H - 2) ^ 2 = (4 * (H - 2)) * H + 4 := by
    have h_cast : ((2 * H - 2 : ℕ) : ℤ) = 2 * (H : ℤ) - 2 := by omega
    have h_cast_right : (((4 * (H - 2)) * H + 4 : ℕ) : ℤ) = 4 * ((H : ℤ) - 2) * (H : ℤ) + 4 := by
      have : 2 ≤ H := by omega
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub this]
      rfl
    exact_mod_cast h_cast ▸ h_cast_right ▸ (by ring : (2 * (H : ℤ) - 2) ^ 2 = 4 * ((H : ℤ) - 2) * (H : ℤ) + 4)
  rw [h2]
  have hH_pos : 0 < H := by omega
  have h3 : ((4 * (H - 2)) * H + 4) / H = 4 * (H - 2) := by
    rw [Nat.add_comm]
    have h_comm : (4 * (H - 2)) * H = H * (4 * (H - 2)) := by ring
    rw [h_comm]
    rw [Nat.add_mul_div_left 4 _ hH_pos]
    have : 4 / H = 0 := Nat.div_eq_of_lt (by omega)
    rw [this, zero_add]
  rw [h3]
  exact Nat.mul_mod_right 4 (H - 2)
