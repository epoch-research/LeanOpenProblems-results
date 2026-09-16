import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma zify_magic (p : ℕ) (hp5 : 5 ≤ p) (hp_odd : Odd p) :
  let c := (p - 1) * (p - 3) / 2
  let M := c * p + 1
  let n := p * (p - 2)
  2 * M = (p - 2) * (n - 1) := by
  intro c M n
  have H0 : 2 * c = (p - 1) * (p - 3) := by
    apply Nat.mul_div_cancel'
    obtain ⟨k, hk⟩ := hp_odd
    have : p - 1 = 2 * k := by omega
    rw [this]
    exact dvd_mul_of_dvd_left (dvd_mul_right 2 k) (p - 3)
  have hp_1 : 1 ≤ p := by omega
  have hp_3 : 3 ≤ p := by omega
  have hp_2 : 2 ≤ p := by omega
  have hp_n : 1 ≤ p * (p - 2) := by
    have : p - 2 ≥ 3 := by omega
    nlinarith
  have hz : (2 * c : ℤ) = (p : ℤ) * p - 4 * p + 3 := by
    have H : (2 * c : ℤ) = ((p - 1) * (p - 3) : ℕ) := by exact_mod_cast H0
    rw [H, Nat.cast_mul, Nat.cast_sub hp_1, Nat.cast_sub hp_3]
    ring
  have H1 : (2 * M : ℤ) = ((p - 2) * (n - 1) : ℕ) := by
    dsimp [M, n]
    rw [Nat.cast_mul, Nat.cast_sub hp_2, Nat.cast_sub hp_n]
    have : (((p * (p - 2)) : ℕ) : ℤ) = p * (p - 2) := by
      rw [Nat.cast_mul, Nat.cast_sub hp_2]
    rw [this]
    have hz2 : (M : ℤ) = c * p + 1 := by
      push_cast
      rfl
    linarith
  exact_mod_cast H1
