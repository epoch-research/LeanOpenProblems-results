import FormalConjectures.Util.ProblemImports
open Nat Finset

lemma zify_magic (p : ℕ) (hp5 : 5 ≤ p) (hp_odd : Odd p) :
  let c := (p - 1) * (p - 3) / 2
  let M := c * p + 1
  let n := p * p - 2 * p
  2 * M = (p - 2) * (n - 1) := by
  intro c M n
  have H0 : 2 * c = (p - 1) * (p - 3) := by
    apply Nat.mul_div_cancel'
    obtain ⟨k, hk⟩ := hp_odd
    have : p - 1 = 2 * k := by omega
    rw [this]
    exact dvd_mul_of_dvd_left (dvd_mul_right 2 k) (p - 3)
  have H1 : (2 * M : ℤ) = ((p - 2) * (n - 1) : ℤ) := by
    dsimp [M, n]
    push_cast
    have hz : (2 : ℤ) * (c : ℤ) = ((p : ℤ) - 1) * ((p : ℤ) - 3) := by
      exact_mod_cast H0
    nlinarith
  exact_mod_cast H1
