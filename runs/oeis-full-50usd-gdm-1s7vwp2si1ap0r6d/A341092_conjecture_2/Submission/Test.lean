import FormalConjectures.Util.ProblemImports

open Nat

lemma choose_succ_succ_eq (N k' : ℕ) :
    Nat.choose N (k' + 2) * (k' + 2) * (k' + 1) = Nat.choose N k' * (N - k') * (N - k' - 1) := by
  have h1 := choose_succ_right_eq N (k' + 1)
  have h2 := choose_succ_right_eq N k'
  calc Nat.choose N (k' + 2) * (k' + 2) * (k' + 1)
    _ = (Nat.choose N (k' + 2) * (k' + 2)) * (k' + 1) := by ring
    _ = (Nat.choose N (k' + 1) * (N - (k' + 1))) * (k' + 1) := by rw [h1]
    _ = (Nat.choose N (k' + 1) * (k' + 1)) * (N - k' - 1) := by
      have : N - (k' + 1) = N - k' - 1 := by omega
      rw [this]
      ring
    _ = (Nat.choose N k' * (N - k')) * (N - k' - 1) := by rw [h2]
    _ = Nat.choose N k' * (N - k') * (N - k' - 1) := by ring

lemma choose_ge_two_mul_self_plus_two {N k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ N / 2) (hN : 2 * k + 4 ≤ N) :
    2 * (k + 2) * (k + 1) ≤ Nat.choose N k := by
  by_cases hk2 : k = 2
  · subst hk2
    have h_eq : Nat.choose N 2 * 2 = N * (N - 1) := by
      have h1 := choose_succ_right_eq N 1
      rw [Nat.choose_one_right] at h1
      exact h1
    have h_ineq : 8 * 7 ≤ N * (N - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  · have hkgt2 : 2 < k := by omega
    have h_lt : Nat.choose N 2 < Nat.choose N k := choose_lt_choose_of_lt_half (by omega) hkN
    have h_eq : Nat.choose N 2 * 2 = N * (N - 1) := by
      have h1 := choose_succ_right_eq N 1
      rw [Nat.choose_one_right] at h1
      exact h1
    let M := (k + 2) * (k + 1)
    have h_calc : 4 * M ≤ N * (N - 1) + 2 := by
      calc 4 * M = 4 * k ^ 2 + 12 * k + 8 := by ring
      _ ≤ 4 * k ^ 2 + 14 * k + 14 := by omega
      _ = (2 * k + 4) * (2 * k + 3) + 2 := by ring
      _ ≤ N * (N - 1) + 2 := by
        have h_ineq : (2 * k + 4) * (2 * k + 3) ≤ N * (N - 1) := Nat.mul_le_mul (by omega) (by omega)
        omega
    have h_omega : 2 * M ≤ Nat.choose N k := by omega
    have h_assoc : 2 * (k + 2) * (k + 1) = 2 * M := by ring
    rw [h_assoc]
    exact h_omega

lemma choose_lt_succ_of_lt_half {n x : ℕ} (h : x < n / 2) : n.choose x < n.choose (x + 1) := by
  have h_eq : n.choose (x + 1) * (x + 1) = n.choose x * (n - x) := choose_succ_right_eq n x
  have h_nx : x + 1 < n - x := by omega
  have h_pos : 0 < n.choose x := by
    have h_xn : x < n := by omega
    exact choose_pos (le_of_lt h_xn)
  have h_mul : n.choose x * (x + 1) < n.choose x * (n - x) := by
    exact Nat.mul_lt_mul_of_pos_left h_nx h_pos
  rw [← h_eq] at h_mul
  exact Nat.lt_of_mul_lt_mul_right h_mul

lemma choose_lt_choose_of_lt_half {n a b : ℕ} (hab : a < b) (hb : b ≤ n / 2) : n.choose a < n.choose b := by
  induction' h_ind : b - a with d ih generalizing a b
  · omega
  · rcases d with _ | d
    · have h_eq : b = a + 1 := by omega
      subst h_eq
      have h_half : a < n / 2 := by omega
      exact choose_lt_succ_of_lt_half h_half
    · have h_lt : a < b - 1 := by omega
      have h_half : b - 1 ≤ n / 2 := by omega
      have ih_res := ih h_lt h_half (by omega)
      have h_half2 : b - 1 < n / 2 := by omega
      have h_step := choose_lt_succ_of_lt_half h_half2
      have h_eq : (b - 1) + 1 = b := by omega
      rw [h_eq] at h_step
      exact ih_res.trans h_step

lemma test (N k' j' : ℕ) (hk'41 : k' ≥ 41) (h_N_ge_2k'6 : N ≥ 2 * k' + 6) (h_N_bound2 : N ≤ 3 * k' + 1) (hj'4 : j' ≥ k' + 3) (h_j'_le_half : j' ≤ N / 2) (h_choose_j'_sub : Nat.choose N j' = 2 * Nat.choose N k' - 1) : False := by
  have hk'10 : k' ≥ 10 := by omega
  have h_choose_j'3_ge : Nat.choose N (k' + 3) ≤ Nat.choose N j' := by
    by_cases hj'_eq : j' = k' + 3
    · rw [hj'_eq]
    · have h_lt3 : k' + 3 < j' := by omega
      exact le_of_lt (choose_lt_choose_of_lt_half h_lt3 h_j'_le_half)
  have h_choose_k3_le : Nat.choose N (k' + 3) * (k' + 3) = Nat.choose N (k' + 2) * (N - (k' + 2)) := choose_succ_right_eq N (k' + 2)
  let C3 := (k' + 1) * (k' + 2) * (k' + 3)
  let A3 := (N - k') * (N - k' - 1) * (N - k' - 2)
  have h_choose_k3_val : Nat.choose N (k' + 3) * C3 = Nat.choose N k' * (N - k') * (N - k' - 1) * (N - k' - 2) := by
    have h_sub_eq : N - (k' + 2) = N - k' - 2 := by omega
    calc Nat.choose N (k' + 3) * C3
      _ = Nat.choose N (k' + 3) * (k' + 3) * (k' + 2) * (k' + 1) := by ring
      _ = (Nat.choose N (k' + 3) * (k' + 3)) * (k' + 2) * (k' + 1) := by ring
      _ = Nat.choose N (k' + 2) * (N - (k' + 2)) * (k' + 2) * (k' + 1) := by rw [h_choose_k3_le]
      _ = (Nat.choose N (k' + 2) * (k' + 2) * (k' + 1)) * (N - k' - 2) := by rw [h_sub_eq]; ring
      _ = Nat.choose N k' * (N - k') * (N - k' - 1) * (N - k' - 2) := by rw [choose_succ_succ_eq N k']
  have h_choose_k3_val2 : Nat.choose N (k' + 3) * C3 = Nat.choose N k' * A3 := by
    calc Nat.choose N (k' + 3) * C3 = Nat.choose N k' * (N - k') * (N - k' - 1) * (N - k' - 2) := h_choose_k3_val
    _ = Nat.choose N k' * A3 := by ring
  have h_C3_val : C3 = k' ^ 3 + 6 * k' ^ 2 + 11 * k' + 6 := by ring
  have h_C3_lt_A3 : 2 * C3 > A3 := by
    have h_A3_le : A3 ≤ (3 * k' + 1 - k') * (3 * k' + 1 - k' - 1) * (3 * k' + 1 - k' - 2) := by
      have hN_k'1 : N - k' ≤ 3 * k' + 1 - k' := by omega
      have hN_k'2 : N - k' - 1 ≤ 3 * k' + 1 - k' - 1 := by omega
      have hN_k'3 : N - k' - 2 ≤ 3 * k' + 1 - k' - 2 := by omega
      exact Nat.mul_le_mul (Nat.mul_le_mul hN_k'1 hN_k'2) hN_k'3
    have h_calc : 2 * C3 + k' ^ 3 ≥ A3 + (3 * k' ^ 2 + 52 * k' + 108) + 1 := by
      calc 2 * C3 + k' ^ 3
        _ = (3 * k' + 1 - k') * (3 * k' + 1 - k' - 1) * (3 * k' + 1 - k' - 2) + (3 * k' ^ 2 + 52 * k' + 108) := by
          have h_sub1 : 3 * k' + 1 - k' = 2 * k' + 1 := by omega
          have h_sub2 : 3 * k' + 1 - k' - 1 = 2 * k' := by omega
          have h_sub3 : 3 * k' + 1 - k' - 2 = 2 * k' - 1 := by omega
          rw [h_sub1, h_sub2, h_sub3, h_C3_val]
          -- both sides are now concrete polynomials in k' with positive coefficients!
          ring
        _ ≥ A3 + (3 * k' ^ 2 + 52 * k' + 108) + 1 := by omega
    omega
  have h_choose_k'_ge : 2 * (k' + 2) * (k' + 1) ≤ Nat.choose N k' := by
    have hk'2 : 2 ≤ k' := by omega
    have h_N_ge_2k'4 : N ≥ 2 * k' + 4 := by omega
    exact choose_ge_two_mul_self_plus_two hk'2 hk'10 h_N_ge_2k'4
  have h_choose_k'_gt : C3 < Nat.choose N k' := by
    have h_rew : 2 * (k' + 2) * (k' + 1) = 2 * (k' + 1) * (k' + 2) := by ring
    rw [h_rew] at h_choose_k'_ge
    have h_C3_lt : C3 < 2 * (k' + 1) * (k' + 2) := by
      calc C3 = (k' + 1) * (k' + 2) * (k' + 3) := by ring
      _ < (k' + 1) * (k' + 2) * (2 * (k' + 1)) := by
        have : k' + 3 < 2 * (k' + 1) := by omega
        -- we can multiply by positive factor
        exact Nat.mul_lt_mul_of_pos_left this (by positivity)
      _ = 2 * (k' + 1) * (k' + 2) * (k' + 1) := by ring
      _ ≤ 2 * (k' + 1) * (k' + 2) * Nat.choose N k' := by
        -- actually, since hk'41 : k' >= 41, we have k'+1 < 2*(k'+1)*(k'+2) <= choose N k'
        sorry
    sorry
  sorry
