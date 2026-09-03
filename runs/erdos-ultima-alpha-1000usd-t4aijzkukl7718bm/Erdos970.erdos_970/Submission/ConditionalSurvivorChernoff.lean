import Submission.RowConditionalVariance

/-! A conditional exponential bound with the actual survivor population and
actual conditional class variances. The new residues are independent after
fixing the old survivor set. Averaging this exponential bound over old phases
requires more than the averaged variance identity. -/
namespace Erdos970.Resampling
open Finset Real Erdos970.GapAverages

lemma residueMean_nonneg (p : ℕ) {f : Fin p → ℝ} (hf : ∀ a, 0 ≤ f a) :
    0 ≤ residueMean p f :=
  div_nonneg (sum_nonneg (fun a _ => hf a)) (by positivity)

/-- The local exponential estimate retains the exact second moment. -/
lemma residueMean_exp_le (p : ℕ) (hp : 0 < p) (f : Fin p → ℝ) (t : ℝ)
    (hmean : residueMean p f = 0) (hsmall : ∀ a, |t * f a| ≤ 1) :
    residueMean p (fun a => exp (t * f a)) ≤
      exp (t ^ 2 * residueMean p (fun a => f a ^ 2)) := by
  have hpoint (a : Fin p) : exp (t * f a) ≤ 1 + t * f a + t ^ 2 * f a ^ 2 := by
    have h := (le_abs_self (exp (t * f a) - 1 - t * f a)).trans
      (abs_exp_sub_one_sub_id_le (hsmall a))
    nlinarith only [h]
  have h := residueMean_mono p hpoint
  rw [residueMean_add, residueMean_add, residueMean_const p hp,
    residueMean_mul, hmean, mul_zero, add_zero, residueMean_mul] at h
  exact h.trans (by linarith only [add_one_le_exp (t ^ 2 * residueMean p (fun a => f a ^ 2))])

/-- Independent-coordinate exponential estimate, with a separate variance
for each coordinate. The boundedness hypothesis is explicit. -/
theorem phaseMean_exp_centered_sum_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : (p : P) → Fin p.val → ℝ) (t : ℝ)
    (hmean : ∀ p : P, residueMean p.val (f p) = 0)
    (hsmall : ∀ (p : P) (a : Fin p.val), |t * f p a| ≤ 1) :
    phaseMean P (fun r => exp (t * ∑ p : P, f p (r p))) ≤
      exp (t ^ 2 * ∑ p : P, residueMean p.val (fun a => f p a ^ 2)) := by
  have he (r : Phase P) : exp (t * ∑ p : P, f p (r p)) =
      ∏ p : P, exp (t * f p (r p)) := by
    rw [mul_sum, exp_sum]
  simp_rw [he]
  rw [phaseMean_prod P (fun p a => exp (t * f p a))]
  change (∏ p : P, residueMean p.val (fun a => exp (t * f p a))) ≤ _
  calc
    _ ≤ ∏ p : P, exp (t ^ 2 * residueMean p.val (fun a => f p a ^ 2)) := by
      apply prod_le_prod
      · intro p hp
        exact residueMean_nonneg _ (fun _ => (exp_pos _).le)
      · intro p hp
        exact residueMean_exp_le p.val (hP p.val p.property).pos (f p) t (hmean p) (hsmall p)
    _ = _ := by rw [← exp_sum, ← mul_sum]

noncomputable def centeredHits (S : Finset ℕ) (p : ℕ) (a : Fin p) : ℝ :=
  classHits S p a - (S.card : ℝ) / p

noncomputable def classVariance (S : Finset ℕ) (p : ℕ) : ℝ :=
  residueMean p (fun a => centeredHits S p a ^ 2)

lemma centeredHits_mean (S : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    residueMean p (centeredHits S p) = 0 := by
  change residueMean p (fun a => classHits S p a - (S.card : ℝ) / p) = _
  rw [residueMean_sub, classHits_mean S p hp, residueMean_const p hp, sub_self]

noncomputable def populationCoveredFraction (S P : Finset ℕ) : ℝ :=
  phaseMean P (fun r => if ∀ x ∈ S, ∃ p : P, x % p.val = (r p).val then 1 else 0)

lemma card_le_total_hits_of_cover (S P : Finset ℕ) (r : Phase P)
    (hcover : ∀ x ∈ S, ∃ p : P, x % p.val = (r p).val) :
    (S.card : ℝ) ≤ ∑ p : P, classHits S p.val (r p) := by
  simp only [classHits]
  rw [sum_comm]
  calc
    (S.card : ℝ) = ∑ x ∈ S, (1 : ℝ) := by simp
    _ ≤ _ := by
      apply sum_le_sum
      intro x hx
      obtain ⟨p, hp⟩ := hcover x hx
      have h := single_le_sum
        (s := (univ : Finset P))
        (f := fun q => if x % q.val = (r q).val then (1 : ℝ) else 0)
        (fun q _ => by dsimp only; split_ifs <;> norm_num) (mem_univ p)
      simpa only [hp, if_true] using h

/-- A valid conditional Chernoff bound for covering the fixed old population.
Its variance term is conditional on that population, not phase-averaged. -/
theorem populationCoveredFraction_le (S P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℝ) (ht : 0 ≤ t)
    (hsmall : ∀ (p : P) (a : Fin p.val), |t * centeredHits S p.val a| ≤ 1) :
    populationCoveredFraction S P ≤ exp
      (-t * (S.card : ℝ) * (1 - ∑ p : P, 1 / (p.val : ℝ)) +
        t ^ 2 * ∑ p : P, classVariance S p.val) := by
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
        linarith
      rw [← exp_add]
      apply one_le_exp_iff.mpr
      nlinarith only [mul_nonneg ht (sub_nonneg.mpr hu)]
    · positivity
  have hm := phaseMean_mono (P := P) hpoint
  rw [phaseMean_mul] at hm
  have hmgf := phaseMean_exp_centered_sum_le P hP (fun p => centeredHits S p.val) t
    (fun p => centeredHits_mean S p.val (hP p.val p.property).pos) hsmall
  have hh := hm.trans (mul_le_mul_of_nonneg_left hmgf (exp_pos _).le)
  change populationCoveredFraction S P ≤ _ at hh
  convert hh using 1
  rw [← exp_add]
  congr 1
  dsimp only [u, classVariance]
  ring

/-- Absolute hit caps imply the bounded centered-increment hypothesis. -/
lemma centeredHits_abs_le (S : Finset ℕ) (p : ℕ) (hp : 0 < p) (B : ℝ)
    (hB : ∀ a : Fin p, classHits S p a ≤ B) (a : Fin p) :
    |centeredHits S p a| ≤ B := by
  have hmean := residueMean_mono p hB
  rw [classHits_mean S p hp, residueMean_const p hp] at hmean
  have hzero : 0 ≤ (S.card : ℝ) / p := by positivity
  rw [centeredHits, abs_le]
  constructor
  · linarith only [classHits_nonneg S p a, hmean]
  · linarith only [hB a, hzero]

/-- Relating the conditional variance to the row variance averaged earlier. -/
lemma classVariance_phaseSurvivors (P : Finset ℕ) (m p : ℕ) (r : Phase P) :
    classVariance (CoverFibers.phaseSurvivors P m r) p = rowConditionalVariance P m p r := by
  simp only [classVariance, centeredHits, rowConditionalVariance, rowCount_eq_classHits,
    CoverFibers.phaseSurvivors_card]

/-- Exact averaged variance budget for several candidate new primes. Unlike
an exponential-moment estimate for this budget, it follows by linearity. -/
theorem mean_classVariance_sum (P R : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (m : ℕ) (hR : ∀ p ∈ R, 0 < p)
    (hc : ∀ p ∈ R, ∀ q ∈ P, p.Coprime q) :
    phaseMean P (fun r => ∑ p ∈ R, classVariance (CoverFibers.phaseSurvivors P m r) p) =
      ∑ p ∈ R,
        (let θ := (m : ℝ) / p - (m / p : ℕ)
         (1 - θ) * countVariance P (m / p) + θ * countVariance P (m / p + 1) +
           density P ^ 2 * θ * (1 - θ) - countVariance P m / (p : ℝ) ^ 2) := by
  rw [phaseMean_sum]
  apply sum_congr rfl
  intro p hp
  simp only [classVariance_phaseSurvivors]
  exact mean_rowConditionalVariance_rounded P hP m p (hR p hp) (hc p hp)

#print axioms phaseMean_exp_centered_sum_le
#print axioms populationCoveredFraction_le
#print axioms centeredHits_abs_le
#print axioms mean_classVariance_sum
end Erdos970.Resampling
