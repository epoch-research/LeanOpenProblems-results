import Submission.Spec
import Mathlib

open Nat Finset

lemma sum_eq_add_sum_Ico_0 {k : ℕ} (f : ℕ → ℕ) (h_0 : 0 < k) :
  ∑ j ∈ range k, f j = f 0 + ∑ j ∈ Ico 1 k, f j := by
  rw [range_eq_Ico]
  have h1 : 0 < k := h_0
  exact sum_eq_sum_Ico_succ_bot h1 f

lemma a_pk_ne_pk_proof_step (p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k) (h_val : p ^ k = ∑ j ∈ range k, (j + 1) * p ^ j) : False := by
  have h_split : ∑ j ∈ range k, (j + 1) * p ^ j = 1 + ∑ j ∈ Ico 1 k, (j + 1) * p ^ j := by
    have h_0 : 0 < k := by omega
    have := sum_eq_add_sum_Ico_0 (fun j => (j + 1) * p ^ j) h_0
    dsimp only at this
    have hz : (0 + 1) * p ^ 0 = 1 := by ring
    rw [hz] at this
    exact this
  rw [h_split] at h_val
  have hdvd1 : p ∣ p ^ k := dvd_pow_self _ (by omega)
  have hdvd2 : p ∣ ∑ j ∈ Ico 1 k, (j + 1) * p ^ j := by
    apply dvd_sum
    intro j hj
    have hj_pos : 0 < j := by
      rw [mem_Ico] at hj
      exact hj.1
    have : p ∣ p ^ j := dvd_pow_self _ (by omega)
    exact dvd_mul_of_dvd_right this _
  have h_dvd3 : p ∣ 1 := by
    have h_sub : 1 = p ^ k - ∑ j ∈ Ico 1 k, (j + 1) * p ^ j := by omega
    rw [h_sub]
    exact Nat.dvd_sub hdvd1 hdvd2
  have h_p1 : p = 1 := Nat.dvd_one.mp h_dvd3
  have h_p_ge2 : 2 ≤ p := hp.two_le
  omega
