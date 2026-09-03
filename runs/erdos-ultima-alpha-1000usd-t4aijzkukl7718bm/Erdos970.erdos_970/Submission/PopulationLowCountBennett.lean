import Submission.ConditionalSurvivorBennett
import Submission.LowCountCylinder

/-! Conditional Bennett bounds for low survivor counts, not just complete
coverage. The old population is fixed throughout each probability estimate. -/
namespace Erdos970.Resampling
open Finset Real Erdos970.GapAverages

/-- Apply independently chosen residue classes to a fixed finite population. -/
def populationSurvivors (S P : Finset ℕ) (r : Phase P) : Finset ℕ :=
  S.filter (fun x => ∀ p : P, x % p.val ≠ (r p).val)

lemma populationSurvivors_card (S P : Finset ℕ) (r : Phase P) :
    ((populationSurvivors S P r).card : ℝ) = ∑ x ∈ S, point P x r := by
  unfold populationSurvivors
  simp_rw [CoverFibers.point_eq_avoidance_indicator]
  exact (sum_boole _ _).symm

lemma card_le_populationSurvivors_add_hits (S P : Finset ℕ) (r : Phase P) :
    (S.card : ℝ) ≤ ((populationSurvivors S P r).card : ℝ) +
      ∑ p : P, classHits S p.val (r p) := by
  rw [populationSurvivors_card]
  simp only [classHits]
  rw [sum_comm, ← sum_add_distrib]
  calc
    (S.card : ℝ) = ∑ _x ∈ S, (1 : ℝ) := by simp
    _ ≤ _ := by
      apply sum_le_sum
      intro x hx
      by_cases ha : ∀ p : P, x % p.val ≠ (r p).val
      · rw [CoverFibers.point_eq_avoidance_indicator, if_pos ha]
        exact le_add_of_nonneg_right (sum_nonneg (fun p _ => by split_ifs <;> norm_num))
      · have he : ∃ p : P, x % p.val = (r p).val := by simpa only [not_forall, not_not] using ha
        obtain ⟨p, hp⟩ := he
        rw [CoverFibers.point_eq_avoidance_indicator, if_neg ha, zero_add]
        have hh := single_le_sum (s := (univ : Finset P))
          (f := fun q => if x % q.val = (r q).val then (1 : ℝ) else 0)
          (fun q _ => by dsimp only; split_ifs <;> norm_num) (mem_univ p)
        simpa only [hp, if_true] using hh

noncomputable def populationLowCountFraction (S P : Finset ℕ) (b : ℝ) : ℝ :=
  phaseMean P (fun r => if ((populationSurvivors S P r).card : ℝ) ≤ b then 1 else 0)

lemma populationLowCountFraction_le_mgf (S P : Finset ℕ) (b t : ℝ) (ht : 0 ≤ t) :
    populationLowCountFraction S P b ≤
      exp (-t * ((S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ)) - b)) *
        phaseMean P (fun r => exp (t * ∑ p : P, centeredHits S p.val (r p))) := by
  let u := (S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ)) - b
  have hpoint (r : Phase P) :
      (if ((populationSurvivors S P r).card : ℝ) ≤ b then (1 : ℝ) else 0) ≤
      exp (-t * u) * exp (t * ∑ p : P, centeredHits S p.val (r p)) := by
    split_ifs with hr
    · have htotal := card_le_populationSurvivors_add_hits S P r
      have hsum : ∑ p : P, centeredHits S p.val (r p) =
          (∑ p : P, classHits S p.val (r p)) -
            (S.card : ℝ) * ∑ p : P, 1 / (p.val : ℝ) := by
        simp only [centeredHits, sum_sub_distrib, mul_sum, mul_one_div]
      have hu : u ≤ ∑ p : P, centeredHits S p.val (r p) := by
        rw [hsum]
        dsimp only [u]
        linarith only [htotal, hr]
      rw [← exp_add]
      apply one_le_exp_iff.mpr
      nlinarith only [mul_nonneg ht (sub_nonneg.mpr hu)]
    · positivity
  have hm := phaseMean_mono P hpoint
  rwa [phaseMean_mul] at hm

/-- Conditional low-tail estimate with arbitrary coordinate caps. -/
theorem populationLowCountFraction_bennett (S P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (b t : ℝ) (ht : 0 ≤ t) (B : P → ℝ)
    (hupper : ∀ (p : P) (a : Fin p.val), centeredHits S p.val a ≤ B p) :
    populationLowCountFraction S P b ≤ exp
      (-t * ((S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ)) - b) +
        ∑ p : P, bennettFactor t (B p) * classVariance S p.val) := by
  have hh := (populationLowCountFraction_le_mgf S P b t ht).trans
    (mul_le_mul_of_nonneg_left (phaseMean_exp_centered_bennett P hP
      (fun p => centeredHits S p.val) B t ht
      (fun p => centeredHits_mean S p.val (hP p.val p.property).pos) hupper) (exp_pos _).le)
  simpa only [classVariance, ← exp_add] using hh

/-- Optimized low-tail form. The deficit u and variance V must have the
stated signs; they are not replaced by averages over other phases. -/
theorem populationLowCountFraction_bennett_optimized (S P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (b B : ℝ) (hB : 0 < B)
    (hupper : ∀ (p : P) (a : Fin p.val), centeredHits S p.val a ≤ B)
    (hu : 0 ≤ (S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ)) - b)
    (hV : 0 < ∑ p : P, classVariance S p.val) :
    let V := ∑ p : P, classVariance S p.val
    let u := (S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ)) - b
    populationLowCountFraction S P b ≤ exp (-(V / B ^ 2 * bennettRate (B * u / V))) := by
  let V := ∑ p : P, classVariance S p.val
  let u := (S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ)) - b
  let t := log (1 + B * u / V) / B
  have hx : 0 ≤ B * u / V := div_nonneg (mul_nonneg hB.le hu) hV.le
  have ht : 0 ≤ t := div_nonneg (log_nonneg (by linarith only [hx])) hB.le
  have hh := populationLowCountFraction_bennett S P hP b t ht (fun _ => B) hupper
  rw [← mul_sum] at hh
  change populationLowCountFraction S P b ≤ exp (-(V / B ^ 2 * bennettRate (B * u / V)))
  exact hh.trans_eq (congrArg exp (bennett_optimized_exponent B V u hB hV hu))

#print axioms card_le_populationSurvivors_add_hits
#print axioms populationLowCountFraction_bennett
#print axioms populationLowCountFraction_bennett_optimized
end Erdos970.Resampling
