import FormalConjectures.Util.ProblemImports
open Nat

lemma candidate_lt_two_mul_N_of_proper_divisor {N d : ℕ} (hN : 6 < N) (hd1 : 1 < d)
    (hdvd : d ∣ N) (hdproper : d < N) :
    (d + 1) * (N / d + 1) < 2 * N := by
  obtain ⟨k, hk⟩ := hdvd
  have hdpos : 0 < d := by omega
  have hkpos : 0 < k := by
    by_contra h
    have : k = 0 := Nat.eq_zero_of_not_pos h
    subst k
    simp at hk
    omega
  have hk_ne1 : k ≠ 1 := by
    intro hk1
    subst k
    simp at hk
    omega
  have hk2 : 2 ≤ k := by omega
  have hNdk : N = d * k := hk
  have hquot : N / d = k := by
    rw [hNdk]
    exact Nat.mul_div_right k hdpos
  have hdk_gt : 6 < d * k := by rwa [← hNdk]
  have hsum_lt : d + k + 1 < d * k := by
    nlinarith [mul_pos (by omega : 0 < d - 1) (by omega : 0 < k - 1)]
  rw [hquot, hNdk]
  nlinarith
