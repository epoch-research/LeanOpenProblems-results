import Submission.Totient.SumKBase
import Submission.Totient.SumKChunk0
import Submission.Totient.SumKChunk1
import Submission.Totient.SumKChunk2
import Submission.Totient.SumKChunk3

open Nat Finset Rat

set_option maxHeartbeats 2000000000
set_option maxRecDepth 20000000

theorem v3_k2_eq_list (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 1807) : 2 * v3_fast k 100 = v3_k2_list.getD k 0 := by
  if h0 : k ≤ 459 then
    exact v3_k2_eq_list_0 k hk1 h0
  else if h1 : k ≤ 919 then
    exact v3_k2_eq_list_1 k (by omega) h1
  else if h2 : k ≤ 1379 then
    exact v3_k2_eq_list_2 k (by omega) h2
  else
    exact v3_k2_eq_list_3 k (by omega) hk2

def my_sum_k2 (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | k + 1 => my_sum_k2 k + v3_k2_list.getD (k + 1) 0

theorem my_sum_k2_1807 : my_sum_k2 1807 = 1798 := rfl

theorem my_sum_k2_eq_Icc (n : ℕ) (hn : n ≤ 1807) : my_sum_k2 n = (Icc 1 n).sum (fun k => 2 * v3_fast k 100) := by
  induction n with
  | zero => simp [my_sum_k2]
  | succ k ih =>
    rw [my_sum_k2, ih (by omega), sum_Icc_succ_top (by omega)]
    have h_eq : v3_k2_list.getD (k + 1) 0 = 2 * v3_fast (k + 1) 100 := by
      exact (v3_k2_eq_list (k + 1) (by omega) (by omega)).symm
    rw [h_eq]

theorem sum_v3_k2_1807 : (Icc 1 1807).sum (fun k => 2 * v3_fast k 100) = 1798 := by
  rw [← my_sum_k2_eq_Icc 1807 (by decide)]
  exact my_sum_k2_1807
