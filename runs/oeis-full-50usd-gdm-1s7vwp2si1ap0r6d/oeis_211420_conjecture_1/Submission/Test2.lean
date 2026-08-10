import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  (8 * n).factorial * n.factorial / ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial)

theorem p_not_dvd_factorial_of_gt {p M : ℕ} (hp : Nat.Prime p) (h : p > M) :
    ¬ p ∣ M.factorial := by
  rw [Nat.Prime.dvd_factorial hp]
  omega

theorem coprime_denominator_of_ge_one (n : ℕ) (hn : n ≥ 1) :
    Nat.Coprime (8 * n - 1) ((4 * n).factorial * (3 * n).factorial * (2 * n).factorial) := by
  apply Nat.coprime_of_dvd
  intro p hp hp_dvd
  intro hp_dvd_Y
  have hp_pos : p > 0 := hp.pos
  have h_8n_1_pos : 8 * n - 1 > 0 := by omega
  have h_le : p ≤ 8 * n - 1 := Nat.le_of_dvd h_8n_1_pos hp_dvd
  have hp_ne_two : p ≠ 2 := by
    intro hp_two
    subst hp_two
    have h_div_8n_1 : 2 ∣ 8 * n - 1 := hp_dvd
    have h_eq : 8 * n - 1 = 2 * (4 * n - 1) + 1 := by omega
    rw [h_eq] at h_div_8n_1
    have h_dvd_left : 2 ∣ 2 * (4 * n - 1) := dvd_mul_right 2 (4 * n - 1)
    have h_dvd_one : 2 ∣ 1 := (Nat.dvd_add_right h_dvd_left).mp h_div_8n_1
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by decide) h_dvd_one
  have hp_ge_two : 2 ≤ p := hp.two_le
  have hp_ge_three : 3 ≤ p := by omega
  sorry
