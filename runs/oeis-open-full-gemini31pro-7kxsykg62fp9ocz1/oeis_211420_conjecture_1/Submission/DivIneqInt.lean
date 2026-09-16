import Mathlib

set_option maxHeartbeats 4000000

lemma div_bound (A M N1 N2 : ℤ) (hM : 0 < M) (h1 : -N1 * M ≤ A) (h2 : A < N2 * M) (q : ℤ) (hq : q * M ≤ A ∧ A < q * M + M) :
  -N1 ≤ q ∧ q < N2 := by
  have H1 : q * M < N2 * M := by omega
  have H2 : -N1 * M < (q + 1) * M := by
    have : (q + 1) * M = q * M + M := by ring
    omega
  have hM_nonneg : 0 ≤ M := by omega
  have H3 : q < N2 := Int.lt_of_mul_lt_mul_right H1 hM_nonneg
  have H4 : -N1 < q + 1 := Int.lt_of_mul_lt_mul_right H2 hM_nonneg
  omega

lemma div_ineq_int (u v M : ℤ) (hM : 0 < M) (hu : 0 ≤ u) (huM : u < M) (hv : 0 ≤ v) (hvM : v < M)
  (q1 : ℤ) (hq1 : q1 * M ≤ 4 * u - v ∧ 4 * u - v < q1 * M + M)
  (q2 : ℤ) (hq2 : q2 * M ≤ 3 * u ∧ 3 * u < q2 * M + M)
  (q3 : ℤ) (hq3 : q3 * M ≤ 2 * u ∧ 2 * u < q3 * M + M)
  (p1 : ℤ) (hp1 : p1 * M ≤ 8 * u - 2 * v ∧ 8 * u - 2 * v < p1 * M + M)
  (p2 : ℤ) (hp2 : p2 * M ≤ 8 * v ∧ 8 * v < p2 * M + M) :
    q1 + q2 + q3 ≤ p1 + p2 := by
  have h_q1_bound : -1 ≤ q1 ∧ q1 < 4 := div_bound (4 * u - v) M 1 4 hM (by omega) (by omega) q1 hq1
  have h_q2_bound : 0 ≤ q2 ∧ q2 < 3 := div_bound (3 * u) M 0 3 hM (by omega) (by omega) q2 hq2
  have h_q3_bound : 0 ≤ q3 ∧ q3 < 2 := div_bound (2 * u) M 0 2 hM (by omega) (by omega) q3 hq3
  have h_p1_bound : -2 ≤ p1 ∧ p1 < 8 := div_bound (8 * u - 2 * v) M 2 8 hM (by omega) (by omega) p1 hp1
  have h_p2_bound : 0 ≤ p2 ∧ p2 < 8 := div_bound (8 * v) M 0 8 hM (by omega) (by omega) p2 hp2
  have H_q1 : q1 = -1 ∨ q1 = 0 ∨ q1 = 1 ∨ q1 = 2 ∨ q1 = 3 := by omega
  have H_q2 : q2 = 0 ∨ q2 = 1 ∨ q2 = 2 := by omega
  have H_q3 : q3 = 0 ∨ q3 = 1 := by omega
  have H_p1 : p1 = -2 ∨ p1 = -1 ∨ p1 = 0 ∨ p1 = 1 ∨ p1 = 2 ∨ p1 = 3 ∨ p1 = 4 ∨ p1 = 5 ∨ p1 = 6 ∨ p1 = 7 := by omega
  have H_p2 : p2 = 0 ∨ p2 = 1 ∨ p2 = 2 ∨ p2 = 3 ∨ p2 = 4 ∨ p2 = 5 ∨ p2 = 6 ∨ p2 = 7 := by omega
  rcases H_q1 with rfl | rfl | rfl | rfl | rfl
  all_goals rcases H_q2 with rfl | rfl | rfl
  all_goals rcases H_q3 with rfl | rfl
  all_goals rcases H_p1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases H_p2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega
