import Mathlib
import Submission.Spec2_part3
import Submission.SpecSum
import Submission.Spec4
import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℤ :=
  Finset.sum (Finset.Ioc 0 n) fun k : ℕ =>
    let k_real : ℝ := k
    let exponent_real : ℝ := k_real * (Real.sqrt 2 - 1)
    let exponent_int : ℤ := Int.floor exponent_real
    (-1 : ℤ) ^ exponent_int.toNat

lemma sum_shift_eq (f : ℕ → ℤ) (P K : ℕ) (h : ∀ k ∈ Finset.Ioc 0 K, f (P + k) = f k) :
  Finset.sum (Finset.Ioc P (P + K)) f = Finset.sum (Finset.Ioc 0 K) f := by
  have H := sum_shift f P K
  rw [H]
  apply Finset.sum_congr rfl
  intro x hx
  exact h x hx

lemma sum_shift_neg (f : ℕ → ℤ) (P K : ℕ) (h : ∀ k ∈ Finset.Ioc 0 K, f (P + k) = - f k) :
  Finset.sum (Finset.Ioc P (P + K)) f = - Finset.sum (Finset.Ioc 0 K) f := by
  have H := sum_shift f P K
  rw [H, ←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  exact h x hx

lemma a_val (N : ℕ) : a N = Finset.sum (Finset.Ioc 0 N) b := by
  unfold a
  apply Finset.sum_congr rfl
  intro k hk
  unfold b
  rfl

lemma a_add (P K : ℕ) (h : ∀ k ∈ Finset.Ioc 0 K, b (P + k) = b k) :
  a (P + K) = a P + a K := by
  rw [a_val (P + K), a_val P, a_val K]
  have H_split : Finset.sum (Finset.Ioc 0 (P + K)) b = Finset.sum (Finset.Ioc 0 P) b + Finset.sum (Finset.Ioc P (P + K)) b := by
    rw [←Finset.sum_union]
    · apply Finset.sum_congr
      · ext x
        rw [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Ioc, Finset.mem_Ioc]
        omega
      · intro x hx
        rfl
    · rw [Finset.disjoint_iff_ne]
      intro a_1 ha b_1 hb
      rw [Finset.mem_Ioc] at ha hb
      omega
  rw [H_split]
  have H_shift := sum_shift_eq b P K h
  rw [H_shift]

lemma a_add_neg (P K : ℕ) (h : ∀ k ∈ Finset.Ioc 0 K, b (P + k) = - b k) :
  a (P + K) = a P - a K := by
  rw [a_val (P + K), a_val P, a_val K]
  have H_split : Finset.sum (Finset.Ioc 0 (P + K)) b = Finset.sum (Finset.Ioc 0 P) b + Finset.sum (Finset.Ioc P (P + K)) b := by
    rw [←Finset.sum_union]
    · apply Finset.sum_congr
      · ext x
        rw [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Ioc, Finset.mem_Ioc]
        omega
      · intro x hx
        rfl
    · rw [Finset.disjoint_iff_ne]
      intro a_1 ha b_1 hb
      rw [Finset.mem_Ioc] at ha hb
      omega
  rw [H_split]
  have H_shift := sum_shift_neg b P K h
  rw [H_shift]
  ring

lemma a_2P_even_zero (j : ℕ) (hj : 0 < j) : a ((2 * P (2*j)).toNat) = 0 := by
  have H_split : (2 * P (2*j)).toNat = (P (2*j)).toNat + (P (2*j)).toNat := by
    have h_pos : 0 ≤ P (2*j) := (PQ_pos (2*j)).1
    rw [←Int.ofNat_inj]
    push_cast
    rw [Int.toNat_of_nonneg (by linarith)]
    rw [Int.toNat_of_nonneg h_pos]
    ring
  rw [H_split]
  have H_neg : ∀ k ∈ Finset.Ioc 0 ((P (2*j)).toNat), b ((P (2*j)).toNat + k) = - b k := by
    intro k hk
    rw [Finset.mem_Ioc] at hk
    rw [add_comm]
    exact b_jump_P_even j k hj hk.1 hk.2
  have H_add := a_add_neg ((P (2*j)).toNat) ((P (2*j)).toNat) H_neg
  rw [H_add]
  ring

lemma a_P_odd_eq_prev (j : ℕ) (hj : 0 < j) : a ((P (2*j+1)).toNat) = a ((P (2*j-1)).toNat) := by
  have H_split : (P (2*j+1)).toNat = (2 * P (2*j)).toNat + (P (2*j-1)).toNat := by
    rw [←Int.ofNat_inj]
    push_cast
    have h_pos_2j : 0 ≤ P (2*j) := (PQ_pos (2*j)).1
    have h_pos_2jm1 : 0 ≤ P (2*j-1) := (PQ_pos (2*j-1)).1
    have h_pos_2jp1 : 0 ≤ P (2*j+1) := (PQ_pos (2*j+1)).1
    rw [Int.toNat_of_nonneg h_pos_2jp1, Int.toNat_of_nonneg (by linarith), Int.toNat_of_nonneg h_pos_2jm1]
    have H_step1 := (PQ_step (2*j)).1
    have H_step2 := (PQ_step (2*j-1)).2
    have H1 : 2*j-1+1 = 2*j := by omega
    have H2 : 2*j+1 = 2*j + 1 := by omega
    have H3 : P (2*j+1) = Q (2*j) + P (2*j) := by rw [H2]; exact H_step1
    have H4 : Q (2*j) = Q (2*j-1) + 2 * P (2*j-1) := by rw [←H1]; exact H_step2
    have H5 : P (2*j) = Q (2*j-1) + P (2*j-1) := by rw [←H1]; exact (PQ_step (2*j-1)).1
    linarith
  rw [H_split]
  have H_shift : ∀ k ∈ Finset.Ioc 0 ((P (2*j-1)).toNat), b ((2 * P (2*j)).toNat + k) = b k := by
    intro k hk
    rw [Finset.mem_Ioc] at hk
    rw [add_comm]
    exact b_jump_2P_even j k hj hk.1 hk.2
  have H_add := a_add ((2 * P (2*j)).toNat) ((P (2*j-1)).toNat) H_shift
  rw [H_add]
  rw [a_2P_even_zero j hj]
  ring

lemma a_P_1 : a ((P 1).toNat) = 1 := by
  have H_P1 : P 1 = 1 := rfl
  have H_toNat : (1:ℤ).toNat = 1 := rfl
  rw [H_P1, H_toNat]
  rw [a_val 1]
  have H_sum : Finset.sum (Finset.Ioc 0 1) b = b 1 := by
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have : Finset.Ioc 0 0 = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [this, Finset.sum_empty, zero_add]
  rw [H_sum]
  have H_b1 : b 1 = 1 := by
    unfold b
    have h1 : Int.floor ((1 : ℝ) * (Real.sqrt 2 - 1)) = 0 := by
      rw [Int.floor_eq_iff]
      have H_bounds : ((0:ℤ):ℝ) ≤ 1 * (Real.sqrt 2 - 1) ∧ 1 * (Real.sqrt 2 - 1) < ((0:ℤ):ℝ) + 1 := by
        push_cast
        constructor
        · have : (1:ℝ) ≤ Real.sqrt 2 := by
            have H : (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
            rw [H]
            apply Real.sqrt_le_sqrt (by norm_num)
          nlinarith
        · have : Real.sqrt 2 < 2 := by
            have H : (2:ℝ) = Real.sqrt 4 := by norm_num
            rw [H]
            apply Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
          nlinarith
      exact H_bounds
    dsimp
    have h2 : ((1:ℕ):ℝ) * (Real.sqrt 2 - 1) = (1:ℝ) * (Real.sqrt 2 - 1) := by push_cast; ring
    rw [h2, h1]
    rfl
  exact H_b1

lemma a_P_odd (j : ℕ) : a ((P (2*j+1)).toNat) = 1 := by
  induction j with
  | zero => exact a_P_1
  | succ j ih =>
    have hj : 0 < j + 1 := by omega
    have H_step := a_P_odd_eq_prev (j + 1) hj
    have H1 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
    rw [H1] at H_step
    rw [H_step]
    exact ih

def M_seq : ℕ → ℕ
| 0 => 0
| (j + 1) => M_seq j + (P (2*j+1)).toNat

lemma M_seq_bound (j : ℕ) : M_seq j ≤ (P (2*j+1)).toNat := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    have h_step : M_seq (j + 1) = M_seq j + (P (2*j+1)).toNat := rfl
    rw [h_step]
    have H_P_pos_1 : 0 ≤ P (2*j+1) := (PQ_pos (2*j+1)).1
    have H_P_pos_2 : 0 ≤ P (2*j+2) := (PQ_pos (2*j+2)).1
    have H_P_pos_3 : 0 ≤ P (2*j+3) := (PQ_pos (2*j+3)).1
    have H1 : P (2*j+2) = Q (2*j+1) + P (2*j+1) := by
      have : 2*j+1+1 = 2*j+2 := by omega
      have h := (PQ_step (2*j+1)).1
      rw [this] at h
      exact h
    have H2 : P (2*j+3) = Q (2*j+2) + P (2*j+2) := by
      have : 2*j+2+1 = 2*j+3 := by omega
      have h := (PQ_step (2*j+2)).1
      rw [this] at h
      exact h
    have H_Q_pos : 0 ≤ Q (2*j+1) := by linarith [(PQ_pos (2*j+1)).2]
    have H_Q2_pos : 0 ≤ Q (2*j+2) := by linarith [(PQ_pos (2*j+2)).2]
    
    have H_ineq : 2 * P (2*j+1) ≤ P (2*j+3) := by
      calc 2 * P (2*j+1) ≤ 2 * P (2*j+1) + Q (2*j+1) := by linarith
        _ = P (2*j+2) + P (2*j+1) := by linarith
        _ ≤ P (2*j+2) + Q (2*j+2) := by 
          have : P (2*j+1) ≤ Q (2*j+2) := by
            have hQ := (PQ_step (2*j+1)).2
            have h_idx : 2*j+1+1 = 2*j+2 := by omega
            rw [h_idx] at hQ
            linarith
          linarith
        _ = P (2*j+3) := by linarith
    
    have H_ineq_nat : 2 * (P (2*j+1)).toNat ≤ (P (2*j+3)).toNat := by
      zify
      rw [Int.toNat_of_nonneg H_P_pos_1, Int.toNat_of_nonneg H_P_pos_3]
      exact H_ineq
      
    have H_idx : 2 * (j + 1) + 1 = 2 * j + 3 := by omega
    rw [H_idx]
    omega

lemma a_M_seq (j : ℕ) : a (M_seq j) = j := by
  induction j with
  | zero => 
    have : M_seq 0 = 0 := rfl
    rw [this, a_val 0]
    have : Finset.Ioc 0 0 = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [this, Finset.sum_empty]
    rfl
  | succ j ih =>
    have H_step : M_seq (j + 1) = M_seq j + (P (2*j+1)).toNat := rfl
    rw [H_step]
    rw [add_comm]
    have H_shift : ∀ k ∈ Finset.Ioc 0 (M_seq j), b ((P (2*j+1)).toNat + k) = b k := by
      intro k hk
      rw [Finset.mem_Ioc] at hk
      rw [add_comm]
      apply b_jump_P_odd j k hk.1
      have H_bound := M_seq_bound j
      omega
    have H_add := a_add ((P (2*j+1)).toNat) (M_seq j) H_shift
    rw [H_add]
    rw [a_P_odd j]
    rw [ih]
    push_cast
    ring

theorem oeis_348295_conjecture_0 : ∀ (M : ℤ), ∃ (n : ℕ), a n > M := by
  intro M
  let j := M.toNat + 1
  use (M_seq j)
  have H : a (M_seq j) = j := a_M_seq j
  rw [H]
  omega

theorem oeis_348295_conjecture_0.disproof : ¬ (type_of% @oeis_348295_conjecture_0) := by
  sorry
