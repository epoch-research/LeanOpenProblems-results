import Submission.GreedyPolynomialFailure

/-!
Unconditional long runs on regular linear four-uniform hypergraphs in a
polynomial parameter family. Every fixed normalized horizon is eventually
valid, with no remaining probabilistic or trajectory assumptions.
-/
namespace Erdos773.GreedyPolynomialExtraction
open Finset Filter GreedyProfileRecords GreedyProfileGuard GreedyGuardControls
open GreedyUniformMoments GreedyUniformCosts GreedyRoundedHorizon GreedyPolynomialFailure
open GreedyTrajectoryCalculus GreedyLinearDrift GreedyHypergraphState
set_option maxHeartbeats 2500000
noncomputable section

structure NumericalData (m : ℕ) (V τ : ℝ) : Prop where
  horizon : Horizon (params m V) (stop V τ) (steps V ((m:ℝ)^4) τ) (16*m) τ
  short : steps V ((m:ℝ)^4) τ ≤ stop V τ
  volume : ((params m V).d)^3 ≤ V
  rho_small : (params m V).rho ≤ 1
  speed_small : speed (params m V) τ ≤ (params m V).d
  failure_small : V^2*(9*(m^12:ℕ)*((steps V ((m:ℝ)^4) τ:ℝ)/(stop V τ:ℝ))^3/((m:ℝ)+1))^(m+1)+
    V*GreedyUniformCosts.failure (params m V) (16*m) τ < 1
  size_lower : V*τ/(2*(m:ℝ)^4) ≤ (steps V ((m:ℝ)^4) τ:ℝ)

lemma eventually_real_le_nat (x : ℝ) : ∀ᶠ m : ℕ in atTop, x ≤ (m:ℝ) :=
  tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop x)

/-- All explicit numerical obligations, uniformly over the polynomial
    volume interval. The threshold depends only on A and tau. -/
theorem eventually_data (A : ℕ) (τ : ℝ) (hτ : 1 ≤ τ) :
    ∀ᶠ m : ℕ in atTop, ∀ V : ℝ, (m:ℝ)^12 ≤ V → V ≤ (m:ℝ)^A → NumericalData m V τ := by
  have hτ0 : 0 ≤ τ := by linarith
  have hq := q_pos τ
  filter_upwards [GreedyUniformHorizon.eventually_bounds 4000 τ (by norm_num) hτ0,
    eventually_real_le_nat 2, eventually_real_le_nat (4/q τ),
    eventually_real_le_nat (4*τ/q τ), eventually_real_le_nat (fixedSpeed τ),
    eventually_real_le_nat (2*auxNumerator τ), eventually_totalBound_lt_one A hτ0]
    with m hb hm hQ hshort hspeed haux hf
  intro V hVlo hVhi
  have hm1 : (1:ℝ) ≤ m := by linarith
  have hmp : (0:ℝ) < m := by linarith
  have hVp : 0 < V := (pow_pos hmp 12).trans_le hVlo
  have hm4 : (m:ℝ) ≤ (m:ℝ)^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hm1 (show 1 ≤ 4 by omega)
  have hmV : (m:ℝ) ≤ V := by
    have hm12 : (m:ℝ) ≤ (m:ℝ)^12 := by
      simpa only [pow_one] using pow_le_pow_right₀ hm1 (show 1 ≤ 12 by omega)
    exact hm12.trans hVlo
  have hQ' : 4 ≤ V*q τ :=
    ((div_le_iff₀ hq).mp hQ).trans (mul_le_mul_of_nonneg_right hmV hq.le)
  have hshort' : 4*τ ≤ (m:ℝ)^4*q τ :=
    ((div_le_iff₀ hq).mp hshort).trans (mul_le_mul_of_nonneg_right hm4 hq.le)
  have hb' := hb V hVlo (16*m) (by norm_num)
  have hh : Horizon (params m V) (stop V τ) (steps V ((m:ℝ)^4) τ) (16*m) τ :=
    GreedyRoundedHorizon.horizon hb' hQ'
  have hdegree : ((params m V).d)^3 ≤ V := by
    dsimp [params]
    simpa only [← pow_mul] using hVlo
  have hρ : (params m V).rho ≤ 1 := by
    exact (div_le_one hmp).mpr hm1
  have hS : speed (params m V) τ ≤ (params m V).d := hspeed.trans hm4
  have haux' : 2*auxNumerator τ ≤ (m:ℝ)+1 := by linarith only [haux]
  have hfailure := (failure_bound hm1 hVp hτ0 hQ' hVhi haux').trans_lt hf
  have hrun : 2 ≤ V*τ/(m:ℝ)^4 := by
    have hm8 : (m:ℝ) ≤ (m:ℝ)^8 := by
      simpa only [pow_one] using pow_le_pow_right₀ hm1 (show 1 ≤ 8 by omega)
    have hdV : (m:ℝ)^8 ≤ V/(m:ℝ)^4 := by
      apply (le_div_iff₀ (pow_pos hmp 4)).mpr
      convert hVlo using 1; ring
    have hVτ : V ≤ V*τ := by nlinarith only [mul_le_mul_of_nonneg_left hτ hVp.le]
    exact (hm.trans hm8).trans (hdV.trans (div_le_div_of_nonneg_right hVτ (pow_nonneg hmp.le 4)))
  exact ⟨hh,steps_le_stop hVp (pow_pos hmp 4) hτ0 hQ' hshort',hdegree,hρ,hS,hfailure,steps_half hrun⟩

/-- Each fixed multiple of V/D^(1/3) is attained eventually in this regular
    linear four-uniform family (D=m^12). The result is unconditional. -/
theorem eventually_independent (A : ℕ) (τ : ℝ) (hτ : 1 ≤ τ) :
    ∀ᶠ m : ℕ in atTop, ∀ (α : Type*) [Fintype α] [DecidableEq α],
      (m:ℝ)^12 ≤ (Fintype.card α:ℝ) → (Fintype.card α:ℝ) ≤ (m:ℝ)^A →
      ∀ H : Finset (Finset α), Linear H → (∀ e ∈ H, e.card = 4) →
      (∀ u : α, HypergraphDegreeTrim.degree H u = m^12) →
      ∃ I : Finset α, Independent H I ∧
        (Fintype.card α:ℝ)*τ/(2*(m:ℝ)^4) ≤ (I.card:ℝ) := by
  filter_upwards [eventually_data A τ hτ] with m hm
  intro α _ _ hVlo hVhi H hlin hfour hregular
  let V : ℝ := Fintype.card α
  have hd := hm V hVlo hVhi
  have hreg : ∀ u : α, (HypergraphDegreeTrim.degree H u:ℝ) = (params m V).d^3 := by
    intro u
    rw [hregular u]
    simp only [params,Nat.cast_pow,← pow_mul]
  obtain ⟨I,hI,hcard⟩ := independent_of_failure hlin hfour (p := params m V) rfl hreg
    (m^12) (fun u => (hregular u).le) hd.horizon hd.short hd.volume hd.rho_small hd.speed_small hd.failure_small
  refine ⟨I,hI,?_⟩
  rw [hcard]
  exact hd.size_lower

#print axioms eventually_data
#print axioms eventually_independent
end
end Erdos773.GreedyPolynomialExtraction
