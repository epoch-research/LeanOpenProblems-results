import Submission.SmoothCutoffSkew

/-! Above the square-root threshold, the smooth-cutoff skew kernel contains
only primes. Its signed reciprocal-discrepancy sum remains unestimated. -/

namespace Erdos371
open Finset

lemma prime_of_large_minFac (D d : ℕ) (hd : 1 < d) (hD : D < d.minFac) (hsize : d ≤ D^2) :
    d.Prime := by
  by_contra hp
  have hs := Nat.minFac_sq_le_self (by omega : 0 < d) hp
  nlinarith

lemma properRoughMoebius_above_sqrt (C d : ℕ) (hsize : d ≤ C^2) :
    properRoughMoebius C d = if d.Prime ∧ C < d then -1 else 0 := by
  by_cases h : 1 < d ∧ C < d.minFac
  · have hp := prime_of_large_minFac C d h.1 h.2 hsize
    have hCd : C < d := by simpa only [hp.minFac_eq] using h.2
    simp [properRoughMoebius,h,hp,hCd,ArithmeticFunction.moebius_apply_prime hp]
  · have hp : ¬ (d.Prime ∧ C < d) := by
      rintro ⟨hp,hCd⟩
      exact h ⟨hp.one_lt,by simpa only [hp.minFac_eq] using hCd⟩
    simp [properRoughMoebius,h,hp]

lemma primeBandMoebius_above_sqrt (B C d : ℕ) (hsize : d ≤ B^2) :
    primeBandMoebius B C d = if d.Prime ∧ B < d ∧ d ≤ C then -1 else 0 := by
  by_cases h : 1 < d ∧ B < d.minFac ∧ d.minFac ≤ C
  · have hp := prime_of_large_minFac B d h.1 h.2.1 hsize
    have hBd : B < d := by simpa only [hp.minFac_eq] using h.2.1
    have hdC : d ≤ C := by simpa only [hp.minFac_eq] using h.2.2
    simp [primeBandMoebius,h,hp,hBd,hdC,ArithmeticFunction.moebius_apply_prime hp]
  · have hp : ¬ (d.Prime ∧ B < d ∧ d ≤ C) := by
      rintro ⟨hp,hBd,hdC⟩
      apply h
      exact ⟨hp.one_lt,by simpa only [hp.minFac_eq] using hBd,by simpa only [hp.minFac_eq] using hdC⟩
    simp [primeBandMoebius,h,hp]

noncomputable def primeBandDiscrepancy (B C N : ℕ) : ℝ :=
  ∑ p ∈ (range (N+2)).filter (fun p => p.Prime ∧ B < p ∧ p ≤ C),
    ∑ q ∈ (range (N+2)).filter (fun q => q.Prime ∧ C < q),
      ((bilinearCount N p q : ℝ)-bilinearCount N q p)

lemma divisorSkewKernel_above_sqrt (B C N : ℕ) (hBC : B ≤ C) (hsize : N+1 ≤ B^2) :
    divisorSkewKernel (primeBandMoebius B C) (properRoughMoebius C) N =
      primeBandDiscrepancy B C N := by
  unfold divisorSkewKernel primeBandDiscrepancy
  rw [sum_filter]
  apply sum_congr rfl
  intro a ha
  have ha' : a ≤ B^2 := (show a ≤ N+1 by have := mem_range.mp ha; omega).trans hsize
  rw [primeBandMoebius_above_sqrt B C a ha']
  by_cases hpa : a.Prime ∧ B < a ∧ a ≤ C
  · rw [if_pos hpa,if_pos hpa,sum_filter]
    apply sum_congr rfl
    intro b hb
    have hb' : b ≤ C^2 := by
      have hbN : b ≤ N+1 := by have := mem_range.mp hb; omega
      nlinarith
    rw [properRoughMoebius_above_sqrt C b hb']
    by_cases hpb : b.Prime ∧ C < b <;> simp [hpb]
  · simp [hpa]

/-- The exact asymmetric smooth-number correlation above the square root
is an endpoint correction plus an unweighted prime-band discrepancy sum. -/
theorem smoothCutoffSkew_above_sqrt (B C N : ℕ) (hB : 1 ≤ B) (hBC : B ≤ C) (hsize : N+1 ≤ B^2) :
    smoothCutoffSkew B C N = smoothIndicator C (N+1)-smoothIndicator B (N+1)+
      primeBandDiscrepancy B C N := by
  rw [smoothCutoffSkew_band_kernel B C N hB hBC,divisorSkewKernel_above_sqrt B C N hBC hsize]

#print axioms smoothCutoffSkew_above_sqrt
end Erdos371
