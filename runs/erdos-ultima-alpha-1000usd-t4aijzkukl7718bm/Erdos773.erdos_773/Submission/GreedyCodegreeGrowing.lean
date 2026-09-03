import Submission.GreedyCodegreeScales
import Submission.GreedyRoundedHorizon

/-!
Uniform nonlinear extraction on regular four-uniform hypergraphs with
bounded pair codegrees. The horizon may grow with m. Every numerical
profile and stopping obligation is discharged below.
-/
namespace Erdos773.GreedyCodegreeGrowing
open Finset Filter GreedyProfileRecords GreedyProfileGuard
open GreedyCodegreeGuardControls GreedyCodegreeScales GreedyCodegreeUniformCosts
open GreedyTrajectoryCalculus GreedyHorizonFactors GreedyRoundedHorizon
open GreedyUniformMoments FourUniformRegularization
set_option maxHeartbeats 2500000
set_option exponentiation.threshold 1024
noncomputable section

def uniformBound (A m : ℕ) : ℝ := 8/(m:ℝ)^2+6*(m:ℝ)^A*Real.exp (-(m:ℝ)/204)

theorem uniformBound_tendsto (A : ℕ) : Tendsto (fun m : ℕ => uniformBound A m) atTop (nhds 0) := by
  have ha := ((tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).pow 2).const_mul 8
  have hr0 := (Real.exp_pos (-(1:ℝ)/204)).le
  have hr1 : Real.exp (-(1:ℝ)/204) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hb := (tendsto_pow_const_mul_const_pow_of_lt_one A hr0 hr1).const_mul 6
  have hexp (m : ℕ) : Real.exp (-(m:ℝ)/204) = Real.exp (-(1:ℝ)/204)^m := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  convert ha.add hb using 1
  · funext m
    simp only [uniformBound,hexp,div_pow,one_pow]
    ring
  · norm_num

structure NumericalData (m : ℕ) (V τ : ℝ) : Prop where
  horizon : Horizon (params m V) (stop V τ) (steps V ((m:ℝ)^100) τ) (16*m^21) τ
  short : steps V ((m:ℝ)^100) τ ≤ stop V τ
  ratio : (steps V ((m:ℝ)^100) τ:ℝ)/(stop V τ:ℝ) ≤ 1/(m:ℝ)^97
  volume : ((params m V).d)^3 ≤ V
  rho_small : (params m V).rho ≤ 1
  speed_small : speed (params m V) τ ≤ (params m V).d
  promotions : PromotionBounds (params m V) (steps V ((m:ℝ)^100) τ) (288*m^133) (54*m^274)
  size_lower : V*τ/(2*(m:ℝ)^100) ≤ (steps V ((m:ℝ)^100) τ:ℝ)

/-- All scalar conditions hold uniformly over horizons with budget at most m.
    The volume lower bound is supplied later by finite regularization. -/
theorem numerical_data {m : ℕ} {V τ : ℝ} (hm : 36 ≤ m) (hτ : 1 ≤ τ)
    (hbudget : horizonBudget τ ≤ (m:ℝ)) (hV : (m:ℝ)^300 ≤ V) : NumericalData m V τ := by
  have hmR : (36:ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by linarith only [hmR]
  have hm0 : (0:ℝ) < m := by linarith only [hmR]
  have hτ0 : 0 ≤ τ := by linarith only [hτ]
  have hVp : 0 < V := (pow_pos hm0 300).trans_le hV
  have hmV : (m:ℝ) ≤ V := by
    apply le_trans _ hV
    simpa only [pow_one] using pow_le_pow_right₀ hm1 (by omega : 1 ≤ 300)
  have hm100 : (m:ℝ) ≤ (m:ℝ)^100 := by
    simpa only [pow_one] using pow_le_pow_right₀ hm1 (by omega : 1 ≤ 100)
  have hQm := (factor_bounds hτ0).2.2.2.1.trans hbudget
  have hshortm := (factor_bounds hτ0).2.2.2.2.trans hbudget
  have hQ : 4 ≤ V*q τ :=
    ((div_le_iff₀ (q_pos τ)).mp hQm).trans (mul_le_mul_of_nonneg_right hmV (q_pos τ).le)
  have hshort : 4*τ ≤ (m:ℝ)^100*q τ :=
    ((div_le_iff₀ (q_pos τ)).mp hshortm).trans (mul_le_mul_of_nonneg_right hm100 (q_pos τ).le)
  have hb := uniform_bounds hτ0 hbudget hV
  have hh : Horizon (params m V) (stop V τ) (steps V ((m:ℝ)^100) τ) (16*m^21) τ :=
    GreedyRoundedHorizon.horizon hb hQ
  have hr : (steps V ((m:ℝ)^100) τ:ℝ)/(stop V τ:ℝ) ≤ 1/(m:ℝ)^97 := by
    apply (ratio_bound hVp (pow_pos hm0 100) hτ0 hQ).trans
    calc
      _ = (4*τ/q τ)/(m:ℝ)^100 := by ring
      _ ≤ (m:ℝ)/(m:ℝ)^100 := div_le_div_of_nonneg_right hshortm (pow_nonneg hm0.le 100)
      _ ≤ _ := by
        apply (div_le_div_iff₀ (pow_pos hm0 100) (pow_pos hm0 97)).mpr
        have hp := pow_le_pow_right₀ hm1 (by omega : 98 ≤ 100)
        nlinarith only [hp]
  have hv : ((params m V).d)^3 ≤ V := by simpa only [params,← pow_mul] using hV
  have hρ : (params m V).rho ≤ 1 := (div_le_one (pow_pos hm0 25)).mpr (one_le_pow₀ hm1)
  have hspeed : speed (params m V) τ ≤ (params m V).d :=
    ((factor_bounds hτ0).2.1.trans hbudget).trans hm100
  have hprom := promotion_bounds_of_uniform hh (promotion_scales (V := V) hτ0 hbudget).1
    (promotion_scales (V := V) hτ0 hbudget).2
  have hrun : 2 ≤ V*τ/(m:ℝ)^100 := by
    have hpow : (m:ℝ) ≤ (m:ℝ)^200 := by
      simpa only [pow_one] using pow_le_pow_right₀ hm1 (by omega : 1 ≤ 200)
    have hdiv : (m:ℝ)^200 ≤ V/(m:ℝ)^100 := by
      apply (le_div_iff₀ (pow_pos hm0 100)).mpr
      simpa only [← pow_add] using hV
    have hVτ : V ≤ V*τ := by nlinarith only [mul_le_mul_of_nonneg_left hτ hVp.le]
    exact (show (2:ℝ) ≤ m by linarith only [hmR]).trans
      (hpow.trans (hdiv.trans (div_le_div_of_nonneg_right hVτ (pow_nonneg hm0.le 100))))
  exact ⟨hh,steps_le_stop hVp (pow_pos hm0 100) hτ0 hQ hshort,hr,hv,hρ,hspeed,hprom,steps_half hrun⟩

/-- A fully proved growing-horizon extraction theorem without linearity.
    Pair codegrees may be m^3, and distinct edges may intersect in two vertices.
    All constants and the volume exponent are uniform over the horizon. -/
theorem eventually_independent (A : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ τ : ℝ, 1 ≤ τ → horizonBudget τ ≤ (m:ℝ) →
      ∀ (α : Type*) [Fintype α] [DecidableEq α],
      (m:ℝ)^300 ≤ (Fintype.card α:ℝ) → (Fintype.card α:ℝ) ≤ (m:ℝ)^A →
      ∀ H : Finset (Finset α), (∀ e ∈ H, e.card = 4) →
      (∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2) →
      (∀ u : α, HypergraphDegreeTrim.degree H u = m^300) →
      (∀ u v : α, u ≠ v → pairDegree H u v ≤ m^3) →
      ∃ I : Finset α, GreedyHypergraphState.Independent H I ∧
        (Fintype.card α:ℝ)*τ/(2*(m:ℝ)^100) ≤ (I.card:ℝ) := by
  filter_upwards [(uniformBound_tendsto A).eventually_lt_const (by norm_num : (0:ℝ) < 1),
    eventually_ge_atTop 36,eventually_ge_atTop A] with m hf hm hAm
  intro τ hτ hbudget α _ _ hVlo hVhi H hfour hinter hregular hcodeg
  let V : ℝ := Fintype.card α
  have hd := numerical_data hm hτ hbudget hVlo
  have hreg : ∀ u : α, (HypergraphDegreeTrim.degree H u:ℝ) = (params m V).d^3 := by
    intro u
    rw [hregular u]
    simp only [params,Nat.cast_pow,← pow_mul]
  have hvolume : Fintype.card α ≤ m^A := by exact_mod_cast hVhi
  have hC : 16*(m^3)^2*m^15 ≤ 16*m^21 := by ring_nf; rfl
  have hcost := GreedyCodegreeUniformCosts.totalCost_bound hd.horizon hd.volume hd.rho_small hd.speed_small (m^3)
  have hprof := profile_failure_bound (by linarith only [hτ] : 0 ≤ τ) hbudget (le_refl (m^3)) V
  have hfail : 8/(m:ℝ)^2+(Fintype.card α:ℝ)*GreedyCodegreeExtraction.totalCost
      (params m V) (m^3) (16*m^21) (steps V ((m:ℝ)^100) τ)
      (fun j _ => GreedyCodegreeUniformCosts.incrementCap (params m V) (m^3) (16*m^21) τ j) < 1 := by
    apply lt_of_le_of_lt _ hf
    unfold uniformBound
    apply add_le_add le_rfl
    have hh := mul_le_mul hVhi (hcost.trans hprof)
      (by unfold GreedyCodegreeExtraction.totalCost GreedyCodegreeExtraction.cost; positivity)
      (by positivity : (0:ℝ) ≤ (m:ℝ)^A)
    nlinarith only [hh]
  obtain ⟨I,hI,hcard⟩ := GreedyCodegreeExtraction.independent_of_certificate hfour hinter
    (p := params m V) rfl hreg (m^300) (m^3) m A hm hAm hvolume
    (fun u => (hregular u).le) hcodeg le_rfl le_rfl hd.horizon hd.short hd.ratio
    hC le_rfl le_rfl hd.promotions
    (fun j _ => GreedyCodegreeUniformCosts.incrementCap (params m V) (m^3) (16*m^21) τ j)
    (fun j _ => GreedyCodegreeUniformCosts.increment_cap_pos hd.horizon (m^3) j)
    (fun j lower n hn => GreedyCodegreeUniformCosts.increment_cap hd.horizon hd.volume hn (m^3) j lower)
    hfail
  refine ⟨I,hI,?_⟩
  rw [hcard]
  exact hd.size_lower

#print axioms uniformBound_tendsto
#print axioms numerical_data
#print axioms eventually_independent
end
end Erdos773.GreedyCodegreeGrowing
