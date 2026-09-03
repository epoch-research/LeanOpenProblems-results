import Submission.BuchstabPrimeCoordinates

/-! Arithmetic tail estimates for the enlarged divisor source, including exact
vanishing on a fixed initial wheel. Both the fixed wheel and the moment error
will be retained when summing the tail. -/
namespace Erdos970.FiniteSelberg
open Finset Real RecursiveSieve RecursiveSieve.Buchstab

noncomputable def scaledPrimeCutoff (L : ℝ) (p : ℕ) : ℕ := selbergCutoff (4*(exp L/(p : ℝ)))
noncomputable def scaledPrimeExcess (L : ℝ) (p : ℕ) : ℝ :=
  (1/(p : ℝ))*(1/primeNormalizer p.primesBelow (scaledPrimeCutoff L p)-1/eulerMass p.primesBelow)

lemma sqrt_exp_eq_exp_half (x : ℝ) : sqrt (exp x) = exp (x/2) := by
  have he : exp x = (exp (x/2))^2 := by
    rw [← exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [he, sqrt_sq (exp_pos _).le]

lemma scaledPrimeCutoff_pos (L : ℝ) (p : ℕ) : 0 < scaledPrimeCutoff L p := by
  unfold scaledPrimeCutoff selbergCutoff
  omega

lemma scaledPrimeCutoff_log_lower (L : ℝ) (p : ℕ) (hp : 0 < p) (hLp : log (p : ℝ) ≤ L) :
    (L-log (p : ℝ))/2 ≤ log (scaledPrimeCutoff L p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have he : exp L/(p : ℝ) = exp (L-log (p : ℝ)) := by rw [exp_sub, exp_log hpR]
  have hD : 1 ≤ exp L/(p : ℝ) := by rw [he]; exact one_le_exp (by linarith)
  have hc := ceiling_sqrt_le_scaledCutoff (exp L/(p : ℝ)) hD
  have hceq : ⌈sqrt (exp L/(p : ℝ))⌉₊ = firstHitCutoff L p := by
    rw [he, sqrt_exp_eq_exp_half]
    rfl
  rw [hceq] at hc
  have hh := log_le_log (show (0 : ℝ) < firstHitCutoff L p by exact_mod_cast firstHitCutoff_pos L p)
    (show (firstHitCutoff L p : ℝ) ≤ scaledPrimeCutoff L p by exact_mod_cast hc)
  exact (firstHitCutoff_log_lower L p).trans hh

lemma scaledPrimeExcess_eq_indexed (i : ℕ) (L : ℝ) :
    scaledPrimeExcess L (nthPrime i) = primeMarginal i*
      (scaledSelbergBase nthPrime i (exp L*primeMarginal i)-prefixDensity primeMarginal i) := by
  have hn := nthPrime_normalizer i (scaledPrimeCutoff L (nthPrime i))
  dsimp only [primeMarginal] at hn
  simp only [scaledPrimeExcess, scaledSelbergBase, selbergBase, primeMarginal,
    nthPrime_prefix_density, mul_one_div]
  rw [← hn]
  rfl

/-- A fixed initial wheel is exactly represented once the divisor level is
large enough. No residual O(1) term remains for these finitely many primes. -/
lemma scaledPrimeExcess_zero_on_wheel (W p : ℕ) (hp : p.Prime) (hpW : p ≤ W)
    (L : ℝ) (hL : (W : ℝ)*(firstHitWheel W : ℝ)^2 ≤ exp L) : scaledPrimeExcess L p = 0 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hWp : (p : ℝ) ≤ W := by exact_mod_cast hpW
  have hD : (firstHitWheel W : ℝ)^2 ≤ exp L/(p : ℝ) := by
    apply (le_div_iff₀ hpR).mpr
    nlinarith [sq_nonneg (firstHitWheel W : ℝ)]
  have hD0 : 0 ≤ exp L/(p : ℝ) := by positivity
  have hQsqrt : (firstHitWheel W : ℝ) ≤ sqrt (4*(exp L/(p : ℝ))) := by
    apply (le_sqrt (Nat.cast_nonneg _) (by positivity)).mpr
    nlinarith
  have hQcut : firstHitWheel W ≤ scaledPrimeCutoff L p :=
    (Nat.le_floor hQsqrt).trans (le_max_right _ _)
  have hsub : p.primesBelow ⊆ (W+1).primesBelow := by
    intro q hq
    obtain ⟨hqp,hqq⟩ := Nat.mem_primesBelow.mp hq
    exact WeightedMertens.mem_primes.mpr ⟨hqq,by omega⟩
  have hprod : (∏ q ∈ p.primesBelow, q) ≤ firstHitWheel W :=
    Nat.le_of_dvd (firstHitWheel_pos W) (prod_dvd_prod_of_subset _ _ id hsub)
  have he := primeNormalizer_eq_eulerMass_of_prod_le p.primesBelow (scaledPrimeCutoff L p)
    (fun q hq => (Nat.mem_primesBelow.mp hq).2) (hprod.trans hQcut)
  simp only [scaledPrimeExcess, he, sub_self, mul_zero]

lemma scaledPrimeExcess_le_ninth_tail (p : ℕ) (hp : p.Prime) (L : ℝ) (hL : 0 < L)
    (hpL : 9*log (p : ℝ) ≤ L)
    (hthreshold : 50*WeightedMertens.sharpMomentError ≤ log (p : ℝ))
    (hthreshold' : supportMassLogThreshold ≤ log (p : ℝ)) :
    scaledPrimeExcess L p ≤ (6*9^8/(217*L^8))*(log (p : ℝ)^7/p) := by
  exact far_normalizer_excess_le p (scaledPrimeCutoff L p) hp (scaledPrimeCutoff_pos L p)
    L hL hpL (scaledPrimeCutoff_log_lower L p hp.pos (by
      have hh := log_natCast_nonneg p
      linarith)) hthreshold hthreshold'

/-- Sharper far-tail coefficient for a truncation at log(p)<=L/13. Using the
coarser ninth-tail coefficient here would needlessly spend the finite margin. -/
lemma scaledPrimeExcess_le_thirteenth_tail (p : ℕ) (hp : p.Prime) (L : ℝ) (hL : 0 < L)
    (hpL : 13*log (p : ℝ) ≤ L)
    (hthreshold : 50*WeightedMertens.sharpMomentError ≤ log (p : ℝ))
    (hthreshold' : supportMassLogThreshold ≤ log (p : ℝ)) :
    scaledPrimeExcess L p ≤ (6*(26/3 : ℝ)^8/(217*L^8))*(log (p : ℝ)^7/p) := by
  let N := scaledPrimeCutoff L p
  let u := log (N : ℝ)/log (p : ℝ)
  have hlogp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hcut := scaledPrimeCutoff_log_lower L p hp.pos (by linarith)
  have hlog : log (N : ℝ) = u*log (p : ℝ) := by dsimp [u]; field_simp
  have hu : 4 ≤ u := by
    apply (le_div_iff₀ hlogp).mpr
    nlinarith only [hcut,hpL,hlogp]
  have hrec := (strict_normalizer_reciprocal_sharp_tail p N hp (scaledPrimeCutoff_pos L p)
    hthreshold hthreshold' u (by linarith) hlog).2
  have hr : 4/u ≤ (26/3 : ℝ)*log (p : ℝ)/L := by
    apply (div_le_div_iff₀ (by linarith : 0 < u) hL).mpr
    change (L-log (p : ℝ))/2 ≤ log (N : ℝ) at hcut
    rw [hlog] at hcut
    nlinarith only [hcut,hpL]
  have hp8 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4/u) hr 8
  have hexp := (rankin_tail_le_eighth_power u hu).trans
    (mul_le_mul_of_nonneg_left hp8 (by norm_num : (0 : ℝ) ≤ 1/7))
  have hh := mul_le_mul_of_nonneg_left
    (hrec.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num))
      (show 0 ≤ 31*log (p : ℝ) by positivity))) (show 0 ≤ 1/(p : ℝ) by positivity)
  convert hh using 1
  field_simp
  <;> ring

#print axioms scaledPrimeExcess_zero_on_wheel
#print axioms scaledPrimeExcess_le_thirteenth_tail
end Erdos970.FiniteSelberg
