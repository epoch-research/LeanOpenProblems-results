import Mathlib

open Finset Nat

theorem c1_step (n k : ℕ) : n.choose k * (n - k) / (k + 1) = n.choose (k + 1) := by
  have H := Nat.choose_succ_right_eq n k
  rw [← H]
  apply Nat.mul_div_cancel
  omega

theorem c2_step (n k : ℕ) (hn : 0 < n) : (n + k - 1).choose k * (n + k) / (k + 1) = (n + (k + 1) - 1).choose (k + 1) := by
  have H := Nat.add_one_mul_choose_eq (n + k - 1) k
  have h_succ : (n + k - 1 + 1) = n + k := by omega
  rw [h_succ] at H
  rw [mul_comm]
  rw [H]
  have H2 : (n + k).choose (k + 1) * (k + 1) / (k + 1) = (n + k).choose (k + 1) := by
    apply Nat.mul_div_cancel; omega
  rw [H2]
  have h_eq : n + k = n + (k + 1) - 1 := by omega
  rw [h_eq]

theorem sum_Ico_succ_bot_eq (k n : ℕ) (h : k < n) (f : ℕ → ℕ) :
  (Finset.Ico k n).sum f = f k + (Finset.Ico (k + 1) n).sum f := by
  have H := Finset.sum_Ico_consecutive f (Nat.le_succ k) h
  have H2 : (Finset.Ico k (k + 1)).sum f = f k := by
    rw [Finset.sum_Ico_succ_top (le_refl _), Finset.Ico_self, Finset.sum_empty, zero_add]
  rw [← H, H2]

def a_fast_loop (n : ℕ) (k : ℕ) (c1 c2 acc : ℕ) : ℕ :=
  if h : k < n then
    let c1' := c1 * (n - k) / (k + 1)
    let c2' := c2 * (n + k) / (k + 1)
    a_fast_loop n (k + 1) c1' c2' (acc + c1^2 * c2^2)
  else
    acc
termination_by n - k

theorem a_fast_loop_eq (d : ℕ) : ∀ (n k c1 c2 acc : ℕ), n - k = d → c1 = n.choose k → c2 = (n + k - 1).choose k → k ≤ n → 0 < n →
  a_fast_loop n k c1 c2 acc = acc + (Finset.Ico k n).sum (fun i => (n.choose i)^2 * ((n + i - 1).choose i)^2) := by
  induction d with
  | zero =>
    intro n k c1 c2 acc hnd hc1 hc2 hk hn
    rw [a_fast_loop]
    split_ifs with h
    · omega
    · rw [Nat.sub_eq_zero_iff_le] at hnd
      have heq : k = n := by omega
      subst heq
      rw [Finset.Ico_self, Finset.sum_empty, add_zero]
  | succ d' ih =>
    intro n k c1 c2 acc hnd hc1 hc2 hk hn
    rw [a_fast_loop]
    split_ifs with h
    · have h_k_le : k + 1 ≤ n := by omega
      have h_d' : n - (k + 1) = d' := by omega
      have hc1' : c1 * (n - k) / (k + 1) = n.choose (k + 1) := by
        rw [hc1]; exact c1_step n k
      have hc2' : c2 * (n + k) / (k + 1) = (n + (k + 1) - 1).choose (k + 1) := by
        rw [hc2]; exact c2_step n k hn
      rw [ih n (k + 1) (c1 * (n - k) / (k + 1)) (c2 * (n + k) / (k + 1)) (acc + c1^2 * c2^2) h_d' hc1' hc2' h_k_le hn]
      rw [sum_Ico_succ_bot_eq k n h]
      have eq1 : (acc + c1 ^ 2 * c2 ^ 2) + ∑ i ∈ Ico (k + 1) n, n.choose i ^ 2 * (n + i - 1).choose i ^ 2 =
                 acc + (c1 ^ 2 * c2 ^ 2 + ∑ i ∈ Ico (k + 1) n, n.choose i ^ 2 * (n + i - 1).choose i ^ 2) := by omega
      rw [eq1, hc1, hc2]
    · omega

def a_fast (n : ℕ) : ℕ := a_fast_loop n 0 1 1 0

theorem a_eq_a_fast_lem (n : ℕ) (hn : 0 < n) : Finset.sum (Finset.range n) (fun k => (n.choose k) ^ 2 * ((n + k - 1).choose k) ^ 2) = a_fast n := by
  have hc1 : 1 = n.choose 0 := (Nat.choose_zero_right n).symm
  have hc2 : 1 = (n + 0 - 1).choose 0 := (Nat.choose_zero_right _).symm
  have eq := a_fast_loop_eq n n 0 1 1 0 (by omega) hc1 hc2 (by omega) hn
  rw [a_fast, eq]
  rw [zero_add]
  have H : Finset.Ico 0 n = Finset.range n := by
    ext x
    simp [Finset.mem_range]
  rw [H]
