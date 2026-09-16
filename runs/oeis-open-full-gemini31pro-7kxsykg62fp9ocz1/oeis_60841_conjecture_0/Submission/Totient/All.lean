import Submission.Totient.Base
import Submission.Totient.Chunk0
import Submission.Totient.Chunk1
import Submission.Totient.Chunk2
import Submission.Totient.Chunk3

open Nat Finset Rat

set_option maxHeartbeats 2000000000
set_option maxRecDepth 20000000

theorem v3_phi_eq_list (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 1807) : v3_fast k.totient 100 = v3_phi_list.getD k 0 := by
  if h0 : k ≤ 459 then
    exact v3_phi_eq_list_0 k hk1 h0
  else if h1 : k ≤ 919 then
    exact v3_phi_eq_list_1 k (by omega) h1
  else if h2 : k ≤ 1379 then
    exact v3_phi_eq_list_2 k (by omega) h2
  else
    exact v3_phi_eq_list_3 k (by omega) hk2

theorem Icc_succ_sum (n : ℕ) (g : ℕ → ℕ) :
  (Icc 1 (n + 1)).sum g = (Icc 1 n).sum g + g (n + 1) := by
  exact sum_Icc_succ_top (by omega) g

theorem my_sum_eq_Icc (n : ℕ) (hn : n ≤ 1807) : my_sum n = (Icc 1 n).sum (fun k => v3_fast k.totient 100) := by
  induction n with
  | zero => simp [my_sum]
  | succ k ih =>
    rw [my_sum, ih (by omega), Icc_succ_sum]
    have h_eq : v3_phi_list.getD (k + 1) 0 = v3_fast (k + 1).totient 100 := by
      exact (v3_phi_eq_list (k + 1) (by omega) (by omega)).symm
    rw [h_eq]

theorem sum_v3_phi_1807 : (Icc 1 1807).sum (fun k => v3_fast k.totient 100) = 1799 := by
  rw [← my_sum_eq_Icc 1807 (by decide)]
  exact my_sum_1807

