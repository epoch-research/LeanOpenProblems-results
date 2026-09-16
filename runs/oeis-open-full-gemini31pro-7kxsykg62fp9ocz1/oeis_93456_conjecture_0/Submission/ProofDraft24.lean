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
  have H1 : 2 * c * p + 2 = (p - 2) * (p * (p - 2) - 1) := by
    zify [show 1 ≤ p by omega, show 3 ≤ p by omega, show 2 ≤ p by omega, show 1 ≤ p * (p - 2) by nlinarith]
    push_cast
    have hz : (2 * c : ℤ) = (p - 1) * (p - 3) := by exact_mod_cast H0
    nlinarith
  -- now H1 implies the goal
  sorry
