import Mathlib
import Submission.Spec
import Submission.Spec2_part3
import Submission.SpecSum
import Submission.Spec4

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
      intro a ha b hb
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
      intro a ha b hb
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
