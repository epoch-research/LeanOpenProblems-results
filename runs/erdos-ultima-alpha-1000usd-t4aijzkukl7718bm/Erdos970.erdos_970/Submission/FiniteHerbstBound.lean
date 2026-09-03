import Submission.PopulationGibbsEntropy

/-! Finite Herbst integration with the coefficient retained explicitly. -/
namespace Erdos970.FiniteGibbs
open Finset Real Filter
open scoped Topology
set_option maxHeartbeats 2000000

variable {α : Type*} [Fintype α] [Nonempty α]

noncomputable def laplace (f : α → ℝ) (t : ℝ) : ℝ := mean (fun a => exp (-t*f a))
noncomputable def laplaceMoment (f : α → ℝ) (t : ℝ) : ℝ :=
  mean (fun a => exp (-t*f a)*f a)
noncomputable def freeEnergy (f : α → ℝ) (t : ℝ) : ℝ := -log (laplace f t)

lemma laplace_pos (f : α → ℝ) (t : ℝ) : 0 < laplace f t := mean_pos (fun _ => exp_pos _)

@[simp] lemma laplace_zero (f : α → ℝ) : laplace f 0 = 1 := by
  simp only [laplace,neg_zero,zero_mul,exp_zero,mean_const]

@[simp] lemma freeEnergy_zero (f : α → ℝ) : freeEnergy f 0 = 0 := by
  simp [freeEnergy]

omit [Nonempty α] in
@[simp] lemma laplaceMoment_zero (f : α → ℝ) : laplaceMoment f 0 = mean f := by
  simp only [laplaceMoment,neg_zero,zero_mul,exp_zero,one_mul]

omit [Nonempty α] in
lemma hasDerivAt_laplace (f : α → ℝ) (t : ℝ) :
    HasDerivAt (laplace f) (-laplaceMoment f t) t := by
  have h (a : α) : HasDerivAt (fun s : ℝ => exp (-s*f a))
      (-(exp (-t*f a)*f a)) t := by
    have hh := ((hasDerivAt_id t).neg.mul_const (f a)).exp
    dsimp at hh
    convert hh using 1
    ring
  have hh := (HasDerivAt.fun_sum (u := (univ : Finset α)) (fun a _ => h a)).div_const
    (Fintype.card α : ℝ)
  simpa only [laplace,laplaceMoment,mean,sum_neg_distrib,neg_div] using hh

lemma hasDerivAt_freeEnergy (f : α → ℝ) (t : ℝ) :
    HasDerivAt (freeEnergy f) (laplaceMoment f t/laplace f t) t := by
  simpa only [freeEnergy,neg_div,neg_neg] using
    ((hasDerivAt_laplace f t).log (laplace_pos f t).ne').neg

omit [Nonempty α] in
lemma entropy_exp_identity (f : α → ℝ) (t : ℝ) :
    entropy (fun a => exp (-t*f a)) =
      laplace f t*freeEnergy f t-t*laplaceMoment f t := by
  have he (a : α) : exp (-t*f a)*log (exp (-t*f a)) =
      -t*(exp (-t*f a)*f a) := by rw [log_exp]; ring
  simp only [entropy,he,mean_mul,laplace,laplaceMoment,freeEnergy]
  ring

/-- A differential inequality from entropy controls the entire finite
Laplace transform on the specified parameter interval. -/
theorem finite_herbst_bound (f : α → ℝ) (A T : ℝ) (hA : 0 ≤ A) (hT : 0 < T)
    (hent : ∀ t ∈ Set.Ioc (0 : ℝ) T,
      entropy (fun a => exp (-t*f a)) ≤ t^2*A*laplaceMoment f t) :
    laplace f T ≤ exp (-(mean f*T/(1+A*T))) := by
  let G := freeEnergy f
  let H := fun t : ℝ => G t*(1+A*t)/t
  have hG (t : ℝ) : HasDerivAt G (laplaceMoment f t/laplace f t) t :=
    hasDerivAt_freeEnergy f t
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt H
      ((t*(1+A*t)*(laplaceMoment f t/laplace f t)-G t)/t^2) t := by
    have hh := ((hG t).mul ((hasDerivAt_const t 1).add
      ((hasDerivAt_id t).const_mul A))).div (hasDerivAt_id t) ht.ne'
    dsimp at hh
    convert hh using 1
    dsimp only [H]
    ring
  have hmono : MonotoneOn H (Set.Ioc (0 : ℝ) T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 T)
    · exact fun t ht => (hd t ht.1).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t ((interior_subset ht).1)).hasDerivWithinAt
    · intro t ht
      have ht' := interior_subset ht
      apply div_nonneg _ (sq_nonneg t)
      have hh := hent t ht'
      rw [entropy_exp_identity] at hh
      have hF := laplace_pos f t
      have hnum : G t*laplace f t ≤ t*(1+A*t)*laplaceMoment f t := by
        dsimp only [G]
        nlinarith only [hh]
      apply (le_div_iff₀ hF).mpr at hnum
      have he : t*(1+A*t)*(laplaceMoment f t/laplace f t) =
          (t*(1+A*t)*laplaceMoment f t)/laplace f t := by ring
      rw [he]
      exact sub_nonneg.mpr hnum
  have hlim : Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 (mean f)) := by
    have hg := (hG 0).tendsto_slope_zero_right
    simp only [G,freeEnergy_zero,zero_add,sub_zero,laplaceMoment_zero,laplace_zero,div_one,
      smul_eq_mul] at hg
    have hc : Tendsto (fun t : ℝ => 1+A*t) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
      have hh : Continuous (fun t : ℝ => 1+A*t) := by fun_prop
      simpa only [mul_zero,add_zero] using
        (hh.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    have hh := hg.mul hc
    convert hh using 1
    · funext t
      dsimp only [H,G]
      ring
    · simp only [mul_one]
  have hμ : mean f ≤ H T := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)] with t ht htT
    exact hmono ⟨ht,htT.le⟩ ⟨hT,le_rfl⟩ htT.le
  have hden : 0 < 1+A*T := by positivity
  have hlo : mean f*T/(1+A*T) ≤ G T := by
    apply (div_le_iff₀ hden).mpr
    have hh := (le_div_iff₀ hT).mp hμ
    exact hh
  rw [← exp_log (laplace_pos f T)]
  apply exp_le_exp.mpr
  dsimp only [G,freeEnergy] at hlo
  linarith only [hlo]

/-- The exact mass of an individual point must be paid when excluding a
zero of a finite random variable. -/
lemma reciprocal_card_le_laplace_of_zero (f : α → ℝ) (t : ℝ) (a : α)
    (ha : f a = 0) : 1/(Fintype.card α : ℝ) ≤ laplace f t := by
  have hh := single_le_sum (s := (univ : Finset α))
    (f := fun a => exp (-t*f a)) (fun _ _ => (exp_pos _).le) (mem_univ a)
  simp only [ha,mul_zero,exp_zero] at hh
  exact div_le_div_of_nonneg_right hh (by positivity)

/-- A sufficient exclusion criterion, not an assertion that the criterion
holds for all arithmetic populations. -/
theorem nonzero_of_finite_herbst (f : α → ℝ) (A T : ℝ) (hA : 0 ≤ A) (hT : 0 < T)
    (hent : ∀ t ∈ Set.Ioc (0 : ℝ) T,
      entropy (fun a => exp (-t*f a)) ≤ t^2*A*laplaceMoment f t)
    (hcost : log (Fintype.card α : ℝ) < mean f*T/(1+A*T)) :
    ∀ a, f a ≠ 0 := by
  intro a ha
  have hu := finite_herbst_bound f A T hA hT hent
  have hl := reciprocal_card_le_laplace_of_zero f T a ha
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have he : exp (-(mean f*T/(1+A*T))) < 1/(Fintype.card α : ℝ) := by
    rw [one_div,← exp_log (inv_pos.mpr hc),log_inv]
    exact exp_lt_exp.mpr (neg_lt_neg hcost)
  exact (hl.trans hu).not_gt he

lemma entropyCapBudget_nonneg (P : Finset ℕ) (B : ℕ → ℝ) (t : ℝ)
    (hB : ∀ p ∈ P, 0 ≤ B p) : 0 ≤ entropyCapBudget P B t := by
  apply sum_nonneg
  intro p hp
  exact div_nonneg (mul_nonneg (by positivity) (hB p hp)) (by positivity)

lemma entropyCapBudget_mono (P : Finset ℕ) (B : ℕ → ℝ)
    (hB : ∀ p ∈ P, 0 ≤ B p) : Monotone (entropyCapBudget P B) := by
  intro s t hst
  apply sum_le_sum
  intro p hp
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right
    (add_le_add le_rfl (exp_le_exp.mpr (mul_le_mul_of_nonneg_right hst (hB p hp)))) (hB p hp)

lemma mean_count (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    mean (count S P) = (S.card : ℝ)*GapAverages.density P := by
  change mean (fun r => ((Resampling.populationSurvivors S P r).card : ℝ)) = _
  simp only [Resampling.populationSurvivors_card]
  rw [mean_phase_eq_phaseMean,GapAverages.phaseMean_sum]
  simp only [GapAverages.phaseMean_point P hP,sum_const,nsmul_eq_mul]

/-- The finite-population Laplace consequence with every deterministic
row cap and its exponential cost still present. -/
theorem population_laplace_cap (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (B : ℕ → ℝ) (T : ℝ) (hT : 0 < T)
    (hB : ∀ p ∈ P, 0 ≤ B p)
    (hcap : ∀ p ∈ P, ∀ a : Fin p, Resampling.classHits S p a ≤ B p) :
    laplace (count S P) T ≤
      exp (-((S.card : ℝ)*GapAverages.density P*T/(1+entropyCapBudget P B T*T))) := by
  letI : Nonempty (GapAverages.Phase P) := phase_nonempty P (fun p hp => (hP p hp).pos)
  rw [← mean_count P S hP]
  apply finite_herbst_bound _ _ T (entropyCapBudget_nonneg P B T hB) hT
  intro t ht
  have hh := population_entropy_cap P S (fun p hp => (hP p hp).pos) B t ht.1.le hB hcap
  apply hh.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (entropyCapBudget_mono P B hB ht.2) (sq_nonneg t))
    (mean_nonneg (fun r => mul_nonneg (exp_pos _).le (by unfold count; positivity)))

/-- A fully explicit sufficient condition for every phase to have a
survivor. In particular the logarithm of the phase-space size is not
silently omitted. -/
theorem population_survivor_of_cap_budget (P S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (B : ℕ → ℝ) (T : ℝ) (hT : 0 < T)
    (hB : ∀ p ∈ P, 0 ≤ B p)
    (hcap : ∀ p ∈ P, ∀ a : Fin p, Resampling.classHits S p a ≤ B p)
    (hcost : log (Fintype.card (GapAverages.Phase P) : ℝ) <
      (S.card : ℝ)*GapAverages.density P*T/(1+entropyCapBudget P B T*T)) :
    ∀ r : GapAverages.Phase P, (Resampling.populationSurvivors S P r).Nonempty := by
  letI : Nonempty (GapAverages.Phase P) := phase_nonempty P (fun p hp => (hP p hp).pos)
  intro r
  by_contra hn
  have hz : count S P r = 0 := by
    simp only [count,Finset.not_nonempty_iff_eq_empty.mp hn,card_empty,Nat.cast_zero]
  have hl := reciprocal_card_le_laplace_of_zero (count S P) T r hz
  have hu := population_laplace_cap P S hP B T hT hB hcap
  have hc : (0 : ℝ) < Fintype.card (GapAverages.Phase P) := by
    exact_mod_cast Fintype.card_pos
  have he : exp (-((S.card : ℝ)*GapAverages.density P*T/(1+entropyCapBudget P B T*T))) <
      1/(Fintype.card (GapAverages.Phase P) : ℝ) := by
    rw [one_div,← exp_log (inv_pos.mpr hc),log_inv]
    exact exp_lt_exp.mpr (neg_lt_neg hcost)
  exact (hl.trans hu).not_gt he

#print axioms finite_herbst_bound
#print axioms nonzero_of_finite_herbst
#print axioms population_laplace_cap
#print axioms population_survivor_of_cap_budget
end Erdos970.FiniteGibbs
