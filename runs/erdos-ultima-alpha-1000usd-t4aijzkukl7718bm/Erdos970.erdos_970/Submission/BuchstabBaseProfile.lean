import Submission.BuchstabScaledSource
import Submission.FirstHitCubeBridge
import Submission.FirstHitDivisorSupport
import Submission.EulerMassNineFifths

/-! Rigorous normalized upper-source profiles on the middle range and the
polynomial tail. These concern the ceiling square-root source dominated by
the enlarged canonical divisor support. -/
namespace Erdos970.FiniteSelberg
open Finset Real Filter

noncomputable def buchstabPrimeCutoff (p : ℕ) (s : ℝ) : ℕ :=
  firstHitCutoff ((s+1)*log (p : ℝ)) p
noncomputable def buchstabBaseRatio (p : ℕ) (s : ℝ) : ℝ :=
  eulerMass p.primesBelow / primeNormalizer p.primesBelow (buchstabPrimeCutoff p s)

lemma buchstabPrimeCutoff_pos (p : ℕ) (s : ℝ) : 0 < buchstabPrimeCutoff p s := firstHitCutoff_pos _ _

lemma buchstabPrimeCutoff_log_lower (p : ℕ) (s : ℝ) :
    (s/2)*log (p : ℝ) ≤ log (buchstabPrimeCutoff p s : ℝ) := by
  have hh := firstHitCutoff_log_lower ((s+1)*log (p : ℝ)) p
  convert hh using 1 <;> ring

lemma buchstabPrimeCutoff_ceiling_sqrt (p : ℕ) (s : ℝ) :
    buchstabPrimeCutoff p s = ⌈sqrt (exp (s*log (p : ℝ)))⌉₊ := by
  have he : exp (s*log (p : ℝ)) = (exp ((s*log (p : ℝ))/2))^2 := by
    rw [← exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [he, sqrt_sq (exp_pos _).le]
  unfold buchstabPrimeCutoff firstHitCutoff
  congr 2
  ring

lemma buchstabBaseRatio_antitone (p : ℕ) (hp : p.Prime) : Antitone (buchstabBaseRatio p) := by
  intro s t hst
  have hcut : buchstabPrimeCutoff p s ≤ buchstabPrimeCutoff p t := by
    apply Nat.ceil_mono
    apply exp_le_exp.mpr
    have hl : 0 ≤ log (p : ℝ) := log_natCast_nonneg p
    nlinarith
  have hG : 0 < primeNormalizer p.primesBelow (buchstabPrimeCutoff p s) :=
    lt_of_lt_of_le (by norm_num) (primeNormalizer_ge_one _ _
      (fun q hq => (Nat.mem_primesBelow.mp hq).2) (buchstabPrimeCutoff_pos p s))
  apply div_le_div_of_nonneg_left
    (eulerMass_pos _ (fun q hq => (Nat.mem_primesBelow.mp hq).2)).le hG
  exact primeNormalizer_cutoff_mono _ (fun q hq => (Nat.mem_primesBelow.mp hq).2) hcut

/-- The available cubic-profile envelope, normalized by the actual Euler mass. -/
theorem buchstabBaseRatio_middle (p : ℕ) (hp : p.Prime) (s : ℝ)
    (hs : 11/10 ≤ s) (hs6 : s ≤ 6)
    (hLp : 20000*firstHitProfileError ≤ log (p : ℝ))
    (hEuler : eulerMass (p+1).primesBelow ≤ (9/5 : ℝ)*log (p : ℝ)) :
    buchstabBaseRatio p s ≤ (90009/50000 : ℝ)*(1/firstHitFullProfile (s/2)) := by
  have hl : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hh := firstHitCutoff_reciprocal_upper_eleven_twentieths
    ((s+1)*log (p : ℝ)) (s/2) p hp hLp (by linarith) (by linarith) (by ring)
  have hM := (eulerMass_strict_prefix_le p hp).trans hEuler
  have hm := mul_le_mul hM hh.2 (one_div_pos.mpr hh.1).le
    (show (0 : ℝ) ≤ (9/5)*log (p : ℝ) by positivity)
  have he : ((9/5 : ℝ)*log (p : ℝ))*
      ((10001/10000 : ℝ)*(1/firstHitFullProfile (s/2))/log (p : ℝ)) =
      (90009/50000 : ℝ)*(1/firstHitFullProfile (s/2)) := by field_simp <;> ring
  rw [he] at hm
  simpa only [buchstabBaseRatio, buchstabPrimeCutoff, mul_one_div] using hm

/-- Keeping the best earlier cutoff avoids any later deterioration of the
cubic lower profile. -/
theorem buchstabBaseRatio_saturated (p : ℕ) (hp : p.Prime) (s : ℝ) (hs : 27/5 ≤ s)
    (hLp : 20000*firstHitProfileError ≤ log (p : ℝ))
    (hEuler : eulerMass (p+1).primesBelow ≤ (9/5 : ℝ)*log (p : ℝ)) :
    buchstabBaseRatio p s ≤ (90009/50000 : ℝ)*(290999/500000 : ℝ) := by
  apply (buchstabBaseRatio_antitone p hp hs).trans
  have hm := buchstabBaseRatio_middle p hp (27/5) (by norm_num) (by norm_num) hLp hEuler
  have hg := firstHitReciprocal_grid_bound 17 (by omega)
  norm_num [firstHitGridUpper] at hg
  have he : 1/firstHitFullProfile ((27/5 : ℝ)/2) = firstHitReciprocal (27/10) := by
    norm_num [firstHitFullProfile, firstHitReciprocal]
  rw [he] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left hg (by norm_num))

/-- A relative eighth-power tail: the Euler mass cancels before any absolute
Euler-product estimate is used. -/
theorem buchstabBaseRatio_eighth_tail (p : ℕ) (hp : p.Prime) (s : ℝ) (hs : 8 ≤ s)
    (hLp : 50*WeightedMertens.sharpMomentError ≤ log (p : ℝ)) :
    buchstabBaseRatio p s ≤ 1+(9/217 : ℝ)*(8/s)^8 := by
  let N := buchstabPrimeCutoff p s
  let E := eulerMass p.primesBelow
  let G := primeNormalizer p.primesBelow N
  let u := log (N : ℝ)/log (p : ℝ)
  let r := exp (-2*(u-3))
  have hN : 0 < N := buchstabPrimeCutoff_pos p s
  have hlogp : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp.one_lt)
  have hu : s/2 ≤ u := (le_div_iff₀ hlogp).mpr (buchstabPrimeCutoff_log_lower p s)
  have hu4 : 4 ≤ u := by linarith
  have hlog : log (N : ℝ) = u*log (p : ℝ) := by dsimp [u]; field_simp
  have hE : 0 < E := eulerMass_pos _ (fun q hq => (Nat.mem_primesBelow.mp hq).2)
  have ht := initial_normalizer_rankin_tail p N hN hLp u hlog
  have hEfull : 0 ≤ eulerMass (p+1).primesBelow :=
    (eulerMass_pos _ (fun q hq => (WeightedMertens.mem_primes.mp hq).1)).le
  have ht' := ht.trans (mul_le_mul_of_nonneg_left (rankin_exponential_le_nine_fortieths u) hEfull)
  have htt := normalizer_strict_prefix_tail hp ((9/40 : ℝ)*r) ht'
  have hr1 : r ≤ 1 := by dsimp [r]; rw [exp_le_one_iff]; linarith
  obtain ⟨hG,hrec⟩ := reciprocal_excess_of_sharp_tail E G r hE (exp_pos _).le hr1
    (by convert htt using 1 <;> dsimp [E,G]; ring)
  have hm := mul_le_mul_of_nonneg_left hrec hE.le
  have hratio : E/G-1 ≤ 9*r/31 := by
    convert hm using 1 <;> field_simp [hE.ne'] <;> ring
  have hratio8 : 4/u ≤ 8/s := by
    apply (div_le_div_iff₀ (by linarith : 0 < u) (by linarith : 0 < s)).mpr
    linarith
  have hp8 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4/u) hratio8 8
  have ht8 := (rankin_tail_le_eighth_power u hu4).trans
    (mul_le_mul_of_nonneg_left hp8 (by norm_num : (0 : ℝ) ≤ 1/7))
  change r ≤ (1/7 : ℝ)*(8/s)^8 at ht8
  change E/G ≤ _
  nlinarith

#print axioms buchstabBaseRatio_middle
#print axioms buchstabBaseRatio_saturated
#print axioms buchstabBaseRatio_eighth_tail
end Erdos970.FiniteSelberg
