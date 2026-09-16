import Submission.MathProof3
import Submission.MathProof
import Submission.Spec
import Mathlib

open Nat List Finset

lemma sum_ge_of_mem {L : List ℕ} {x : ℕ} (hx : x ∈ L) : x ≤ L.sum := by
  induction L with
  | nil => contradiction
  | cons y ys ih =>
    cases hx with
    | head _ => exact Nat.le_add_right _ _
    | tail _ hxt =>
      have := ih hxt
      exact le_trans this (Nat.le_add_left _ _)

lemma pairwise_lt_of_le_and_nodup {L : List ℕ} (h1 : L.Pairwise (· ≤ ·)) (h2 : L.Nodup) : L.Pairwise (· < ·) := by
  induction L with
  | nil => exact Pairwise.nil
  | cons x xs ih =>
    have h1t := Pairwise.of_cons h1
    have h2t := Nodup.of_cons h2
    have ihs := ih h1t h2t
    apply Pairwise.cons
    · intro y hy
      have hle : x ≤ y := rel_of_pairwise_cons h1 hy
      have hne : x ≠ y := by
        intro heq
        rw [← heq] at hy
        have hnot : x ∉ xs := (nodup_cons.mp h2).1
        contradiction
      omega
    · exact ihs

lemma a_le_minFac (n : ℕ) (hn : n ≥ 2) : a n ≤ minFac n := by
  let p := minFac n
  let L := (Nat.divisors n).sort (· ≤ ·)
  have hp : p = minFac n := rfl
  have hn0 : n ≠ 0 := by omega
  have h_p_dvd : p ∣ n := minFac_dvd n
  have h_np_dvd : (n/p) ∣ n := Nat.div_dvd_of_dvd h_p_dvd
  have h_p_gt_1 : p ≥ 2 := minFac_prime (by omega) |>.two_le
  have h_n_in : n ∈ L := by
    rw [mem_sort, Nat.mem_divisors]
    exact ⟨dvd_rfl, hn0⟩
  have h_np_in : n/p ∈ L := by
    rw [mem_sort, Nat.mem_divisors]
    exact ⟨h_np_dvd, hn0⟩
  have h_np_lt_n : n/p < n := Nat.div_lt_self (by omega) h_p_gt_1
  have hS_le : L.Pairwise (· ≤ ·) := pairwise_sort _ _
  have hNodup : L.Nodup := sort_nodup _ _
  have hS : L.Pairwise (· < ·) := pairwise_lt_of_le_and_nodup hS_le hNodup
  
  have h_adj : (n/p, n) ∈ List.zip L L.tail := by
    apply adjacent_of_no_between hS h_np_in h_n_in h_np_lt_n
    intro x hx h_bet
    have hx_dvd : x ∣ n := by
      rw [mem_sort, Nat.mem_divisors] at hx
      exact hx.1
    exact no_divisor_between hn hp h_bet.1 h_bet.2 hx_dvd
  
  have h_prod_in : (n/p) * n ∈ List.map (fun p : ℕ × ℕ => p.fst * p.snd) (List.zip L L.tail) := by
    apply List.mem_map.mpr
    exact ⟨(n/p, n), h_adj, rfl⟩
  
  have h_prod_le_sum : (n/p) * n ≤ (List.map (fun p : ℕ × ℕ => p.fst * p.snd) (List.zip L L.tail)).sum := by
    exact sum_ge_of_mem h_prod_in
  
  have h_prod_eq : (n/p) * n = n^2 / p := by
    have h1 : n * (n/p) = n^2 / p := by
      rw [pow_two]
      exact (Nat.mul_div_assoc n h_p_dvd).symm
    rw [mul_comm]
    exact h1

  have h_s_ge : n^2 / p ≤ (List.map (fun p : ℕ × ℕ => p.fst * p.snd) (List.zip L L.tail)).sum := by
    rw [← h_prod_eq]
    exact h_prod_le_sum

  unfold a
  dsimp only
  
  split
  · exact Nat.zero_le p
  · next h_s_not_zero =>
    have hp_pos : p > 0 := by omega
    have hs : (List.map (fun p : ℕ × ℕ => p.fst * p.snd) (List.zip L L.tail)).sum > 0 := by
      have : (List.map (fun p : ℕ × ℕ => p.fst * p.snd) (List.zip L L.tail)).sum ≠ 0 := h_s_not_zero
      omega
    have h2 : n^2 ≤ (List.map (fun p : ℕ × ℕ => p.fst * p.snd) (List.zip L L.tail)).sum * p := by
      have h3 : p ∣ n^2 := by
        rw [pow_two]
        exact dvd_mul_of_dvd_left h_p_dvd n
      have h4 : n^2 / p * p = n^2 := Nat.div_mul_cancel h3
      have h5 : n^2 / p * p ≤ (List.map (fun p : ℕ × ℕ => p.fst * p.snd) (List.zip L L.tail)).sum * p := Nat.mul_le_mul_right p h_s_ge
      omega
    
    have h_div1 : n^2 / (List.map (fun p : ℕ × ℕ => p.fst * p.snd) (List.zip L L.tail)).sum ≤ ((List.map (fun p : ℕ × ℕ => p.fst * p.snd) (List.zip L L.tail)).sum * p) / (List.map (fun p : ℕ × ℕ => p.fst * p.snd) (List.zip L L.tail)).sum := Nat.div_le_div_right h2
    have h_div2 : ((List.map (fun p : ℕ × ℕ => p.fst * p.snd) (List.zip L L.tail)).sum * p) / (List.map (fun p : ℕ × ℕ => p.fst * p.snd) (List.zip L L.tail)).sum = p := Nat.mul_div_cancel_left p hs
    
    have s_list_def : List.map (fun p : ℕ × ℕ ↦ p.fst * p.snd) (List.zip ((Nat.divisors n).sort (· ≤ ·)) ((Nat.divisors n).sort (· ≤ ·)).tail) = List.map (fun p : ℕ × ℕ => p.fst * p.snd) (List.zip L L.tail) := rfl
    
    rw [s_list_def]
    rw [h_div2] at h_div1
    exact h_div1
