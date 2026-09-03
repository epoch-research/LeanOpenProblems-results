import Submission.FirstHitNormalizedCost

/-! Two reference cutoff scales. These definitions do not change the
conjecture or the prime budget. -/
namespace Erdos970.FiniteSelberg
open Finset Real

noncomputable def twoScaleParameter (L : ℝ) (p : ℕ) : ℝ :=
  if log (p : ℝ) ≤ L/100 then L/2 else L
noncomputable def twoScaleCutoff (L : ℝ) (p : ℕ) : ℕ :=
  firstHitCutoff (twoScaleParameter L p) p
noncomputable def twoScaleSmallCut (L : ℝ) : ℕ := ⌊exp (L/100)⌋₊
noncomputable def twoScaleMainSum (L : ℝ) : ℝ :=
  ∑ p ∈ (saturatedHitPrimeCut L 0+1).primesBelow,
    (1/(p : ℝ))/primeNormalizer p.primesBelow (twoScaleCutoff L p)

lemma twoScaleCutoff_pos (L : ℝ) (p : ℕ) : 0 < twoScaleCutoff L p :=
  firstHitCutoff_pos _ _

lemma twoScaleSmallCut_pos (L : ℝ) (hL : 0 ≤ L) : 0 < twoScaleSmallCut L := by
  change 1 ≤ ⌊exp (L/100)⌋₊
  exact Nat.le_floor (by simpa using one_le_exp (show 0 ≤ L/100 by positivity))

lemma log_le_twoScaleSmallCut (L : ℝ) (p : ℕ) (hp : 0 < p) :
    log (p : ℝ) ≤ L/100 ↔ p ≤ twoScaleSmallCut L := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [twoScaleSmallCut, Nat.le_floor_iff (exp_pos _).le]
  exact (log_le_iff_le_exp hp0)

lemma twoScaleSmallCut_log_le (L : ℝ) (hL : 0 ≤ L) :
    log (twoScaleSmallCut L : ℝ) ≤ L/100 := by
  exact (log_le_twoScaleSmallCut L _ (twoScaleSmallCut_pos L hL)).mpr le_rfl

lemma primeNormalizer_le_eulerMass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    primeNormalizer P N ≤ eulerMass P := by
  rw [← primeWeight_sum_eq_eulerMass P hP]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    (fun Q hQ _ => primeWeight_nonneg Q (fun p hp => hP p (mem_powerset.mp hQ hp)))

lemma firstHitMeanExcess_nonneg (L : ℝ) (p : ℕ) (hp : p.Prime) :
    0 ≤ firstHitMeanExcess L p := by
  have hP : ∀ q ∈ p.primesBelow, q.Prime := fun q hq => (Nat.mem_primesBelow.mp hq).2
  have hG := primeNormalizer_ge_one p.primesBelow (firstHitCutoff L p) hP (firstHitCutoff_pos L p)
  have hh := one_div_le_one_div_of_le (by linarith : 0 < primeNormalizer p.primesBelow (firstHitCutoff L p))
    (primeNormalizer_le_eulerMass p.primesBelow hP (firstHitCutoff L p))
  exact mul_nonneg (by positivity) (sub_nonneg.mpr hh)

lemma reference_canonical_cost_at_scale (k : ℕ) (i : Fin k) (T : ℝ)
    (hT : 2*log (firstPrimeList k i : ℝ) ≤ T) :
    kernelCost (fun j => 1/(firstPrimeList k j : ℝ))
      (canonicalOrthogonal (fun j => 1/(firstPrimeList k j : ℝ))
        (priorDivisorSupport (firstPrimeList k) i (firstHitCutoff T (firstPrimeList k i))))^2 ≤
      (64*exp 4*exp T) * (1/((firstPrimeList k i : ℝ)*log (firstPrimeList k i)^2)) := by
  let p := firstPrimeList k
  let q := fun j => 1/(p j : ℝ)
  let R := firstHitCutoff T (p i)
  let D := priorDivisorSupport p i R
  have hp := firstPrimeList_prime k
  have hpinj := (firstPrimeList_strictMono k).injective
  have hlp : 0 < log (p i : ℝ) := log_pos (by exact_mod_cast (hp i).one_lt)
  have hG := primeNormalizer_strict_log_lower (p i) R (hp i)
    (firstHitCutoff_pos T _) ((by change 2*log (p i : ℝ) ≤ T at hT; linarith :
      log (p i : ℝ)/2 ≤ (T-log (p i))/2).trans (firstHitCutoff_log_lower T _))
  rw [← reference_prior_normalizer k i R] at hG
  have hc := prime_canonical_cost_le_of_subset p hp hpinj R D
    (priorDivisorSupport_nonempty p i R (firstHitCutoff_pos T _)) (filter_subset _ _)
  have hu : kernelCost q (canonicalOrthogonal q D) ≤ 4*exp 2*(R : ℝ)/log (p i) := by
    calc
      _ ≤ exp 2*(R : ℝ)/normalizer q D := hc
      _ ≤ exp 2*(R : ℝ)/(log (p i)/4) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hG
      _ = _ := by ring
  have hc0 : 0 ≤ kernelCost q (canonicalOrthogonal q D) := sum_nonneg (fun _ _ => abs_nonneg _)
  have hs := pow_le_pow_left₀ hc0 hu 2
  have hR := firstHitCutoff_sq_le T (p i) (hp i).pos
    (by change 2*log (p i : ℝ) ≤ T at hT; linarith)
  have hR' := mul_le_mul_of_nonneg_left hR (show 0 ≤ 16*exp 4 / log (p i)^2 by positivity)
  have he : (exp (2 : ℝ))^2 = exp 4 := by rw [← exp_nat_mul]; norm_num
  rw [div_pow, mul_pow, mul_pow, he] at hs
  norm_num only [show (4 : ℝ)^2 = 16 by norm_num] at hs
  change (R : ℝ)^2 ≤ _ at hR
  convert hs.trans (by convert hR' using 1 <;> ring) using 1 <;> ring

#print axioms reference_canonical_cost_at_scale
end Erdos970.FiniteSelberg
