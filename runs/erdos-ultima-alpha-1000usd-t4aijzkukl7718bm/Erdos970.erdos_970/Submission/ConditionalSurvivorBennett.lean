import Submission.ConditionalSurvivorChernoff
import Submission.BennettAnalytic

/-! A full one-sided Bennett estimate for independent new residue coordinates,
conditional on a fixed old survivor population. The actual variance is retained;
no substitution of its mean inside an exponential is made. -/
namespace Erdos970.Resampling
open Finset Real Erdos970.GapAverages

lemma residueMean_exp_bennett (p : ℕ) (hp : 0 < p) (f : Fin p → ℝ)
    (t B : ℝ) (ht : 0 ≤ t) (hmean : residueMean p f = 0)
    (hupper : ∀ a, f a ≤ B) :
    residueMean p (fun a => exp (t * f a)) ≤
      exp (bennettFactor t B * residueMean p (fun a => f a ^ 2)) := by
  have h := residueMean_mono p (fun a => exp_le_bennett t B (f a) ht (hupper a))
  rw [residueMean_add, residueMean_add, residueMean_const p hp,
    residueMean_mul, hmean, mul_zero, add_zero, residueMean_mul] at h
  exact h.trans (by linarith only [add_one_le_exp (bennettFactor t B * residueMean p (fun a => f a ^ 2))])

/-- Different coordinates can use different one-sided caps. -/
theorem phaseMean_exp_centered_bennett (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : (p : P) → Fin p.val → ℝ) (B : P → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hmean : ∀ p : P, residueMean p.val (f p) = 0)
    (hupper : ∀ (p : P) (a : Fin p.val), f p a ≤ B p) :
    phaseMean P (fun r => exp (t * ∑ p : P, f p (r p))) ≤
      exp (∑ p : P, bennettFactor t (B p) * residueMean p.val (fun a => f p a ^ 2)) := by
  have he (r : Phase P) : exp (t * ∑ p : P, f p (r p)) =
      ∏ p : P, exp (t * f p (r p)) := by rw [mul_sum, exp_sum]
  simp_rw [he]
  rw [phaseMean_prod P (fun p a => exp (t * f p a))]
  change (∏ p : P, residueMean p.val (fun a => exp (t * f p a))) ≤ _
  calc
    _ ≤ ∏ p : P, exp (bennettFactor t (B p) * residueMean p.val (fun a => f p a ^ 2)) := by
      apply prod_le_prod
      · intro p hp
        exact residueMean_nonneg _ (fun _ => (exp_pos _).le)
      · intro p hp
        exact residueMean_exp_bennett p.val (hP p.val p.property).pos (f p)
          t (B p) ht (hmean p) (hupper p)
    _ = _ := (exp_sum _ _).symm

/-- The elementary Chernoff step, separate from any chosen MGF bound. -/
lemma populationCoveredFraction_le_mgf (S P : Finset ℕ) (t : ℝ) (ht : 0 ≤ t) :
    populationCoveredFraction S P ≤
      exp (-t * (S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ))) *
        phaseMean P (fun r => exp (t * ∑ p : P, centeredHits S p.val (r p))) := by
  let u : ℝ := (S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ))
  have hpoint (r : Phase P) :
      (if ∀ x ∈ S, ∃ p : P, x % p.val = (r p).val then (1 : ℝ) else 0) ≤
      exp (-t * u) * exp (t * ∑ p : P, centeredHits S p.val (r p)) := by
    split_ifs with hr
    · have htotal := card_le_total_hits_of_cover S P r hr
      have hsum : ∑ p : P, centeredHits S p.val (r p) =
          (∑ p : P, classHits S p.val (r p)) -
            (S.card : ℝ) * ∑ p : P, 1 / (p.val : ℝ) := by
        simp only [centeredHits, sum_sub_distrib, mul_sum, mul_one_div]
      have hu : u ≤ ∑ p : P, centeredHits S p.val (r p) := by
        rw [hsum]
        dsimp only [u]
        linarith only [htotal]
      rw [← exp_add]
      apply one_le_exp_iff.mpr
      nlinarith only [mul_nonneg ht (sub_nonneg.mpr hu)]
    · positivity
  have hm := phaseMean_mono P hpoint
  rw [phaseMean_mul] at hm
  simpa only [u, mul_assoc] using hm

/-- Conditional Bennett inequality, without the earlier small-increment
restriction. Each variance remains that of the fixed population S. -/
theorem populationCoveredFraction_bennett (S P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℝ) (ht : 0 ≤ t) (B : P → ℝ)
    (hupper : ∀ (p : P) (a : Fin p.val), centeredHits S p.val a ≤ B p) :
    populationCoveredFraction S P ≤ exp
      (-t * (S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ)) +
        ∑ p : P, bennettFactor t (B p) * classVariance S p.val) := by
  have hh := (populationCoveredFraction_le_mgf S P t ht).trans
    (mul_le_mul_of_nonneg_left (phaseMean_exp_centered_bennett P hP
      (fun p => centeredHits S p.val) B t ht
      (fun p => centeredHits_mean S p.val (hP p.val p.property).pos) hupper) (exp_pos _).le)
  simpa only [classVariance, ← exp_add] using hh

/-- Optimizing the Laplace parameter for a common positive cap. The positive
variance hypothesis is explicit, so no division by a zero variance is hidden. -/
theorem populationCoveredFraction_bennett_optimized (S P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (B : ℝ) (hB : 0 < B)
    (hupper : ∀ (p : P) (a : Fin p.val), centeredHits S p.val a ≤ B)
    (hρ : (∑ p : P, 1 / (p.val : ℝ)) ≤ 1)
    (hV : 0 < ∑ p : P, classVariance S p.val) :
    let V := ∑ p : P, classVariance S p.val
    let u := (S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ))
    populationCoveredFraction S P ≤ exp (-(V / B ^ 2 * bennettRate (B * u / V))) := by
  let V := ∑ p : P, classVariance S p.val
  let u := (S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ))
  have hu : 0 ≤ u := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hρ)
  let t := log (1 + B * u / V) / B
  have hx : 0 ≤ B * u / V := div_nonneg (mul_nonneg hB.le hu) hV.le
  have ht : 0 ≤ t := div_nonneg (log_nonneg (by linarith only [hx])) hB.le
  have hh := populationCoveredFraction_bennett S P hP t ht (fun _ => B) hupper
  rw [← mul_sum] at hh
  change populationCoveredFraction S P ≤ exp (-(V / B ^ 2 * bennettRate (B * u / V)))
  have he : -t * (S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ)) +
      bennettFactor t B * V = -(V / B ^ 2 * bennettRate (B * u / V)) := by
    have hid := bennett_optimized_exponent B V u hB hV hu
    convert hid using 1 <;> dsimp only [t, u] <;> ring
  rwa [he] at hh

lemma bennettRate_log_lower (x : ℝ) (hx : 0 ≤ x) (hlog : 2 ≤ log (1 + x)) :
    x / 2 * log (1 + x) ≤ bennettRate x := by
  unfold bennettRate
  nlinarith only [hlog, mul_nonneg hx (by linarith only [hlog] : 0 ≤ log (1 + x) - 2)]

/-- Explicit logarithmic gain in the large-deviation, small-variance regime. -/
theorem populationCoveredFraction_bennett_log (S P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (B : ℝ) (hB : 0 < B)
    (hupper : ∀ (p : P) (a : Fin p.val), centeredHits S p.val a ≤ B)
    (hρ : (∑ p : P, 1 / (p.val : ℝ)) ≤ 1)
    (hV : 0 < ∑ p : P, classVariance S p.val)
    (hlog : 2 ≤ log (1 + B * ((S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ))) /
      (∑ p : P, classVariance S p.val))) :
    let V := ∑ p : P, classVariance S p.val
    let u := (S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ))
    populationCoveredFraction S P ≤ exp (-(u / (2 * B) * log (1 + B * u / V))) := by
  let V := ∑ p : P, classVariance S p.val
  let u := (S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ))
  have hu : 0 ≤ u := mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hρ)
  have hh := populationCoveredFraction_bennett_optimized S P hP B hB hupper hρ hV
  apply hh.trans
  apply exp_le_exp.mpr
  have hl := mul_le_mul_of_nonneg_left (bennettRate_log_lower (B * u / V)
    (div_nonneg (mul_nonneg hB.le hu) hV.le) hlog)
    (div_nonneg hV.le (sq_nonneg B))
  have he : V / B ^ 2 * (B * u / V / 2 * log (1 + B * u / V)) =
      u / (2 * B) * log (1 + B * u / V) := by
    have hVp : 0 < V := hV
    field_simp [hVp.ne', hB.ne']
  rw [he] at hl
  exact neg_le_neg hl

#print axioms phaseMean_exp_centered_bennett
#print axioms populationCoveredFraction_bennett_optimized
#print axioms populationCoveredFraction_bennett_log
end Erdos970.Resampling
