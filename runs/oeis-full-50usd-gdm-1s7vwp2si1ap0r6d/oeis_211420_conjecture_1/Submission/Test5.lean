import FormalConjectures.Util.ProblemImports

open Nat

theorem div_eq_of_lt_of_le {a b c : ℕ} (hb : 0 < b) (h1 : b * c ≤ a) (h2 : a < b * (c + 1)) : a / b = c := by
  have h1' : c * b ≤ a := by rwa [mul_comm] at h1
  have h2' : a < (c + 1) * b := by rwa [mul_comm] at h2
  have h3 : c ≤ a / b := (Nat.le_div_iff_mul_le hb).mpr h1'
  have h4 : a / b < c + 1 := (Nat.div_lt_iff_lt_mul hb).mpr h2'
  omega

theorem ratio_inequality (r P : ℕ) (hP : 0 < P) (hr : r < P) :
    4 * r / P + 3 * r / P + 2 * r / P ≤ 8 * r / P := by
  have h_cases :
    8 * r < P ∨
    (P ≤ 8 * r ∧ 4 * r < P) ∨
    (4 * r ≥ P ∧ 3 * r < P) ∨
    (3 * r ≥ P ∧ 8 * r < 3 * P) ∨
    (8 * r ≥ 3 * P ∧ 2 * r < P) ∨
    (2 * r ≥ P ∧ 8 * r < 5 * P) ∨
    (8 * r ≥ 5 * P ∧ 3 * r < 2 * P) ∨
    (3 * r ≥ 2 * P ∧ 4 * r < 3 * P) ∨
    (4 * r ≥ 3 * P ∧ 8 * r < 7 * P) ∨
    (8 * r ≥ 7 * P) := by omega
  rcases h_cases with h | h | h | h | h | h | h | h | h | h
  · have h1 : 4 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 2 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 2 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 0 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 3 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 2 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 4 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 2 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 5 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 2 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 2 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 5 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 3 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 2 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 6 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega
  · have h1 : 4 * r / P = 3 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h2 : 3 * r / P = 2 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h3 : 2 * r / P = 1 := div_eq_of_lt_of_le hP (by omega) (by omega)
    have h4 : 8 * r / P = 7 := div_eq_of_lt_of_le hP (by omega) (by omega)
    omega

theorem n_div_P_relation (n P : ℕ) (hP : 0 < P) :
    4 * n / P = 4 * (n / P) + (4 * (n % P)) / P := by
  have h_eq : 4 * n = 4 * (n % P) + P * (4 * (n / P)) := by
    nth_rw 1 [← Nat.div_add_mod n P]
    ring
  rw [h_eq]
  rw [Nat.add_mul_div_left (4 * (n % P)) (4 * (n / P)) hP]
  omega

theorem div_add_div_eq (n P : ℕ) (hP : 0 < P) :
    4 * n / P + 3 * n / P + 2 * n / P ≤ 8 * n / P + n / P := by
  have h4 : 4 * n / P = 4 * (n / P) + (4 * (n % P)) / P := n_div_P_relation n P hP
  have h3 : 3 * n / P = 3 * (n / P) + (3 * (n % P)) / P := by
    have h_eq : 3 * n = 3 * (n % P) + P * (3 * (n / P)) := by
      nth_rw 1 [← Nat.div_add_mod n P]
      ring
    rw [h_eq]
    rw [Nat.add_mul_div_left (3 * (n % P)) (3 * (n / P)) hP]
    omega
  have h2 : 2 * n / P = 2 * (n / P) + (2 * (n % P)) / P := by
    have h_eq : 2 * n = 2 * (n % P) + (2 * (n / P)) * P := by
      nth_rw 1 [← Nat.div_add_mod n P]
      ring
    rw [h_eq]
    have h_comm : 2 * (n % P) + (2 * (n / P)) * P = 2 * (n % P) + P * (2 * (n / P)) := by ring
    rw [h_comm]
    rw [Nat.add_mul_div_left (2 * (n % P)) (2 * (n / P)) hP]
    omega
  have h8 : 8 * n / P = 8 * (n / P) + (8 * (n % P)) / P := by
    have h_eq : 8 * n = 8 * (n % P) + P * (8 * (n / P)) := by
      nth_rw 1 [← Nat.div_add_mod n P]
      ring
    rw [h_eq]
    rw [Nat.add_mul_div_left (8 * (n % P)) (8 * (n / P)) hP]
    omega
  have hr : n % P < P := Nat.mod_lt n hP
  have hineq := ratio_inequality (n % P) P hP hr
  omega
