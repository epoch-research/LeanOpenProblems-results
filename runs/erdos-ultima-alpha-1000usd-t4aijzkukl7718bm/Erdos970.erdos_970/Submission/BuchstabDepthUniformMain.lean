import Submission.BuchstabContinuousMain

/-! Uniformity in refinement depth for the fixed-level, fixed-slack main-term
transfer. The prime threshold still depends on the level and slack; no rate
as the level approaches two is asserted. -/
namespace Erdos970.ContinuousBuchstab
open Real Finset Set MeasureTheory
set_option maxHeartbeats 1600000

lemma upperEnvelope_antitone_depth (s : ℝ) (hs : 1 ≤ s) :
    Antitone (fun n => upperEnvelope n s) :=
  antitone_nat_of_succ_le (fun n => upperEnvelope_succ_le n s hs)

/-- The geometric tail estimate is uniform over every later refinement. -/
theorem upperEnvelope_later_difference (N n : ℕ) (hNn : N ≤ n)
    (s : ℝ) (hs : 1 ≤ s) :
    |upperEnvelope N s-upperEnvelope n s| ≤ 40000*(19/20 : ℝ)^N*exp (-s) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hNn
  have hanti := upperEnvelope_antitone_depth s hs (Nat.le_add_right N r)
  rw [abs_of_nonneg (sub_nonneg.mpr hanti)]
  have hh := sum_le_sum (s := range r) (fun i _ =>
    (le_abs_self (upperEnvelope (N+i) s-upperEnvelope (N+i+1) s)).trans
      (upperEnvelope_difference_bound (N+i) s hs))
  have he : (∑ i ∈ range r, (upperEnvelope (N+i) s-upperEnvelope (N+i+1) s)) =
      upperEnvelope N s-upperEnvelope (N+r) s := by
    simpa only [Nat.add_zero,Nat.add_assoc] using
      sum_range_sub' (fun i => upperEnvelope (N+i) s) r
  rw [he] at hh
  have hsum : (∑ i ∈ range r, 2000*(19/20 : ℝ)^(N+i)*exp (-s)) =
      (2000*(19/20 : ℝ)^N*exp (-s))*(∑ i ∈ range r, (19/20 : ℝ)^i) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [pow_add]
    ring
  rw [hsum] at hh
  have hg : (∑ i ∈ range r, (19/20 : ℝ)^i) ≤ 20 := by
    have h := geom_sum_mul_neg (19/20 : ℝ) r
    have hp : 0 ≤ (19/20 : ℝ)^r := by positivity
    norm_num only [show (1 : ℝ)-19/20=1/20 by norm_num] at h
    linarith only [h,hp]
  have hb := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ 2000*(19/20 : ℝ)^N*exp (-s) by positivity)
  exact hh.trans (by convert hb using 1; ring)

lemma upperEnvelope_later_difference_coarse (N n : ℕ) (hNn : N ≤ n)
    (s : ℝ) (hs : 1 ≤ s) :
    upperEnvelope N s-upperEnvelope n s ≤ 40000*(19/20 : ℝ)^N := by
  have he : exp (-s) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  exact ((le_abs_self _).trans (upperEnvelope_later_difference N n hNn s hs)).trans
    (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left he
      (show 0 ≤ 40000*(19/20 : ℝ)^N by positivity)))

/-- The corresponding lower profiles have the same uniform depth-tail control.
This is independent of any arithmetic prime-sum approximation. -/
theorem lowerProfile_later_difference (N n : ℕ) (hNn : N ≤ n)
    (s : ℝ) (hs : 2 ≤ s) :
    lowerProfile n s-lowerProfile N s ≤ 40000*(19/20 : ℝ)^N := by
  let C : ℝ := 40000*(19/20 : ℝ)^N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha : 1 ≤ s-1 := by linarith
  have hsub := abs_tailIntegral_le (fun v => upperEnvelope N v-upperEnvelope n v)
    ((measurable_upperEnvelope N).sub (measurable_upperEnvelope n)) C (s-1)
    (fun v hv => upperEnvelope_later_difference N n hNn v hv) ha
  have hiN := (upperEnvelope_integrable N).mono_set (Ioi_subset_Ioi ha)
  have hin := (upperEnvelope_integrable n).mono_set (Ioi_subset_Ioi ha)
  unfold tailIntegral at hsub
  rw [integral_sub hiN hin] at hsub
  have hlo : lowerProfile n s-lowerProfile N s =
      (tailIntegral (upperEnvelope N) (s-1)-tailIntegral (upperEnvelope n) (s-1))/s := by
    unfold lowerProfile
    ring
  rw [hlo]
  have htail : tailIntegral (upperEnvelope N) (s-1)-tailIntegral (upperEnvelope n) (s-1) ≤
      C*exp (-(s-1)) := (le_abs_self _).trans hsub
  have hdiv := div_le_div_of_nonneg_right htail (show 0 ≤ s by linarith)
  have he : exp (-(s-1)) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hh := mul_le_mul_of_nonneg_left he hC
  simp only [mul_one] at hh
  exact hdiv.trans ((div_le_self (mul_nonneg hC (exp_pos _).le) (by linarith : 1 ≤ s)).trans hh)

end Erdos970.ContinuousBuchstab

namespace Erdos970.RecursiveSieve.Buchstab
open Real Finset ContinuousBuchstab
set_option maxHeartbeats 1600000

lemma referenceUpper_antitone_depth (k : ℕ) (D : ℝ) :
    Antitone (fun n => referenceUpper n k D) :=
  antitone_nat_of_succ_le (fun n => referenceUpper_succ_le n k D)

lemma referenceLower_monotone_depth (k : ℕ) (D : ℝ) :
    Monotone (fun n => referenceLower n k D) :=
  monotone_nat_of_le_succ (fun n => referenceLower_succ_ge n k D)

/-- One prime threshold works for ALL refinement depths at a fixed upper
level and fixed positive approximation slack. -/
theorem upperModelApprox_uniform_depth (s : ℝ) (hs : 1 ≤ s) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n k : ℕ, K ≤ nthPrime k →
      referenceUpper n k (exp (s*log (nthPrime k : ℝ))) ≤
        prefixDensity primeMarginal k*(1+upperEnvelope n s+ε) := by
  classical
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < ε/80000 by positivity) (by norm_num : (19/20 : ℝ) < 1)
  have htail : 40000*(19/20 : ℝ)^N ≤ ε/2 := by linarith only [hN]
  choose H hH using (fun i : Fin (N+1) =>
    (continuous_model_transfer i.val).1 s hs (ε/2) (by positivity))
  let K := univ.sup H
  have hfinite (i : ℕ) (hi : i ≤ N) (k : ℕ) (hk : K ≤ nthPrime k) :
      referenceUpper i k (exp (s*log (nthPrime k : ℝ))) ≤
        prefixDensity primeMarginal k*(1+upperEnvelope i s+ε/2) := by
    exact hH ⟨i,by omega⟩ k ((le_sup (f := H) (mem_univ ⟨i,by omega⟩)).trans hk)
  refine ⟨K,fun n k hk => ?_⟩
  by_cases hn : n ≤ N
  · exact (hfinite n hn k hk).trans (mul_le_mul_of_nonneg_left (by linarith)
      (nthPrime_prefix_density_pos k).le)
  · have hNn : N ≤ n := by omega
    have hh := (referenceUpper_antitone_depth k _ hNn).trans (hfinite N le_rfl k hk)
    have hd := (upperEnvelope_later_difference_coarse N n hNn s hs).trans htail
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith only [hd])
      (nthPrime_prefix_density_pos k).le)

/-- The lower comparison is likewise uniform in depth, while its prime
threshold still depends on the chosen level s and the slack ε. -/
theorem lowerModelApprox_uniform_depth (s : ℝ) (hs : 2 ≤ s) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n k : ℕ, K ≤ nthPrime k →
      prefixDensity primeMarginal k*(lowerProfile n s-ε) ≤
        referenceLower n k (exp (s*log (nthPrime k : ℝ))) := by
  classical
  obtain ⟨N,hN⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < ε/80000 by positivity) (by norm_num : (19/20 : ℝ) < 1)
  have htail : 40000*(19/20 : ℝ)^N ≤ ε/2 := by linarith only [hN]
  choose H hH using (fun i : Fin (N+1) =>
    (continuous_model_transfer i.val).2 s hs (ε/2) (by positivity))
  let K := univ.sup H
  have hfinite (i : ℕ) (hi : i ≤ N) (k : ℕ) (hk : K ≤ nthPrime k) :
      prefixDensity primeMarginal k*(lowerProfile i s-ε/2) ≤
        referenceLower i k (exp (s*log (nthPrime k : ℝ))) := by
    exact hH ⟨i,by omega⟩ k ((le_sup (f := H) (mem_univ ⟨i,by omega⟩)).trans hk)
  refine ⟨K,fun n k hk => ?_⟩
  by_cases hn : n ≤ N
  · exact (mul_le_mul_of_nonneg_left (by linarith : lowerProfile n s-ε ≤ lowerProfile n s-ε/2)
      (nthPrime_prefix_density_pos k).le).trans (hfinite n hn k hk)
  · have hNn : N ≤ n := by omega
    have hd := (lowerProfile_later_difference N n hNn s hs).trans htail
    have hh := (mul_le_mul_of_nonneg_left
      (show lowerProfile n s-ε ≤ lowerProfile N s-ε/2 by linarith only [hd])
      (nthPrime_prefix_density_pos k).le).trans (hfinite N le_rfl k hk)
    exact hh.trans (referenceLower_monotone_depth k _ hNn)

/-- Combined depth-uniform transfer. This quantifier order does NOT provide a
rate allowing s=s(k)→2 or ε=ε(k)→0. -/
theorem continuous_model_transfer_uniform_depth (s : ℝ) (hs : 2 ≤ s) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n k : ℕ, K ≤ nthPrime k →
      referenceUpper n k (exp (s*log (nthPrime k : ℝ))) ≤
        prefixDensity primeMarginal k*(1+upperEnvelope n s+ε) ∧
      prefixDensity primeMarginal k*(lowerProfile n s-ε) ≤
        referenceLower n k (exp (s*log (nthPrime k : ℝ))) := by
  obtain ⟨Ku,hKu⟩ := upperModelApprox_uniform_depth s (by linarith) ε hε
  obtain ⟨Kl,hKl⟩ := lowerModelApprox_uniform_depth s hs ε hε
  exact ⟨max Ku Kl,fun n k hk =>
    ⟨hKu n k ((le_max_left _ _).trans hk),hKl n k ((le_max_right _ _).trans hk)⟩⟩

#print axioms upperEnvelope_later_difference
#print axioms lowerProfile_later_difference
#print axioms upperModelApprox_uniform_depth
#print axioms lowerModelApprox_uniform_depth
#print axioms continuous_model_transfer_uniform_depth
end Erdos970.RecursiveSieve.Buchstab
