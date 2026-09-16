import Mathlib
import Submission.Spec
import Submission.Proof12

open Nat BigOperators

lemma vp_P_lower_bound (n p : ℕ) [Fact p.Prime] (hn2 : n > 2) (hodd : p > 2) :
  (n - 2) / (p - 1) ≤ padicValNat p ((Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1)) := by
  have hdvd := p_pow_dvd_P n p hn2 hodd
  have hpos := P_pos n hn2
  have hne : (Finset.Ico 1 (n - 1)).prod (fun k => 2 ^ k - 1) ≠ 0 := by omega
  exact (padicValNat_dvd_iff_le hne).mp hdvd
