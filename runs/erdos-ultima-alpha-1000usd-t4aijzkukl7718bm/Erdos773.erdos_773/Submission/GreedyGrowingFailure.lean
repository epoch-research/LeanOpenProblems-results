import Submission.GreedyHorizonFactors
import Submission.GreedyPolynomialExtraction

/-!
A failure envelope uniform in a logarithmically growing normalized horizon.
The polynomial parameter m is specialized to n^2, so all horizon factors
bounded by n leave an exponential-in-n concentration estimate.
-/
namespace Erdos773.GreedyGrowingFailure
open Finset Filter GreedyProfileRecords GreedyProfileGuard GreedyUniformMoments
open GreedyUniformCosts GreedyRoundedHorizon GreedyPolynomialFailure
open GreedyPolynomialExtraction GreedyHorizonFactors GreedyTrajectoryCalculus
set_option maxHeartbeats 2500000
noncomputable section

def uniformBound (A n : ℕ) : ℝ :=
  (n:ℝ)^(4*A)*(1/2:ℝ)^(n+1)+6*(n:ℝ)^(2*A)*Real.exp (-(n:ℝ)/68)

lemma totalBound_uniform {A n : ℕ} {τ : ℝ} (hn : 1 ≤ n) (hτ : 0 ≤ τ)
    (hP : fixedPenalty τ ≤ (n:ℝ)) : totalBound A (n^2) τ ≤ uniformBound A n := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hPpos := fixedPenalty_pos hτ
  have hdiv : (n:ℝ)/68 ≤ (n:ℝ)^2/(68*fixedPenalty τ) := by
    apply (div_le_div_iff₀ (by norm_num) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left hP hnpos.le
    nlinarith only [hh]
  have hexp : Real.exp (-((n^2:ℕ):ℝ)/(68*fixedPenalty τ)) ≤ Real.exp (-(n:ℝ)/68) := by
    apply Real.exp_le_exp.mpr
    simpa only [Nat.cast_pow,neg_div,neg_le_neg_iff] using hdiv
  have hn2 : n ≤ n^2 := by nlinarith
  have hpow : (1/2:ℝ)^(n^2+1) ≤ (1/2:ℝ)^(n+1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have he1 : (((n^2:ℕ):ℝ))^(2*A) = (n:ℝ)^(4*A) := by
    rw [Nat.cast_pow,← pow_mul]
    congr 1
    omega
  have he2 : (((n^2:ℕ):ℝ))^A = (n:ℝ)^(2*A) := by rw [Nat.cast_pow,← pow_mul]
  unfold totalBound uniformBound
  rw [he1,he2]
  exact add_le_add (mul_le_mul_of_nonneg_left hpow (by positivity))
    (mul_le_mul_of_nonneg_left hexp (by positivity))

lemma uniformBound_tendsto (A : ℕ) : Tendsto (fun n : ℕ => uniformBound A n) atTop (nhds 0) := by
  have hr0 : 0 ≤ Real.exp (-(1:ℝ)/68) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(1:ℝ)/68) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have ha := (tendsto_pow_const_mul_const_pow_of_lt_one (4*A)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).mul_const (1/2:ℝ)
  have hb := (tendsto_pow_const_mul_const_pow_of_lt_one (2*A) hr0 hr1).const_mul 6
  have hexp (n : ℕ) : Real.exp (-(n:ℝ)/68) = Real.exp (-(1:ℝ)/68)^n := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  convert ha.add hb using 1
  · funext n
    simp only [uniformBound,hexp,pow_succ]
    ring
  · norm_num

/-- The threshold in n is UNIFORM over all tau satisfying
    exp(10000*(1+tau)^3)<=n. In particular tau may grow with n. -/
theorem eventually_uniform_data (A : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ τ : ℝ, 1 ≤ τ → horizonBudget τ ≤ (n:ℝ) →
      ∀ V : ℝ, (((n^2:ℕ):ℝ))^12 ≤ V → V ≤ (((n^2:ℕ):ℝ))^A →
      NumericalData (n^2) V τ := by
  filter_upwards [(uniformBound_tendsto A).eventually_lt_const (by norm_num : (0:ℝ) < 1),
    eventually_ge_atTop 2] with n hf hn
  intro τ hτ hbudget V hVlo hVhi
  let m := n^2
  have hτ0 : 0 ≤ τ := by linarith only [hτ]
  have hn1 : 1 ≤ n := by omega
  have hn2 : n ≤ m := by dsimp [m]; nlinarith
  have hnreal : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnm : (n:ℝ) ≤ m := by exact_mod_cast hn2
  have hm : (2:ℝ) ≤ m := hnreal.trans hnm
  have hm1 : (1:ℝ) ≤ m := by linarith only [hm]
  have hmp : (0:ℝ) < m := by linarith only [hm]
  have hVp : 0 < V := (pow_pos hmp 12).trans_le hVlo
  have hq := q_pos τ
  obtain ⟨hP,hS,haux,hQ,hshort⟩ := factor_bounds hτ0
  have hP' : fixedPenalty τ ≤ (n:ℝ) := hP.trans hbudget
  have hbudgetm : horizonBudget τ ≤ (m:ℝ) := hbudget.trans hnm
  have hQm : 4/q τ ≤ (m:ℝ) := hQ.trans hbudgetm
  have hshortm : 4*τ/q τ ≤ (m:ℝ) := hshort.trans hbudgetm
  have hspeedm : fixedSpeed τ ≤ (m:ℝ) := hS.trans hbudgetm
  have hm4 : (m:ℝ) ≤ (m:ℝ)^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hm1 (show 1 ≤ 4 by omega)
  have hmV : (m:ℝ) ≤ V := by
    have hm12 : (m:ℝ) ≤ (m:ℝ)^12 := by
      simpa only [pow_one] using pow_le_pow_right₀ hm1 (show 1 ≤ 12 by omega)
    exact hm12.trans hVlo
  have hQ' : 4 ≤ V*q τ :=
    ((div_le_iff₀ hq).mp hQm).trans (mul_le_mul_of_nonneg_right hmV hq.le)
  have hshort' : 4*τ ≤ (m:ℝ)^4*q τ :=
    ((div_le_iff₀ hq).mp hshortm).trans (mul_le_mul_of_nonneg_right hm4 hq.le)
  have hb := GreedyUniformHorizon.exponential_threshold (m:ℝ) V τ (16*m) hτ0 hbudgetm hVlo (by norm_num)
  have hh : Horizon (params m V) (stop V τ) (steps V ((m:ℝ)^4) τ) (16*m) τ :=
    GreedyRoundedHorizon.horizon hb hQ'
  have hdegree : ((params m V).d)^3 ≤ V := by
    dsimp [params]
    simpa only [← pow_mul] using hVlo
  have hρ : (params m V).rho ≤ 1 := (div_le_one hmp).mpr hm1
  have hspeed : speed (params m V) τ ≤ (params m V).d := hspeedm.trans hm4
  have haux' : 2*auxNumerator τ ≤ (m:ℝ)+1 := by
    have hh' := haux.trans hbudget
    dsimp [m]
    push_cast
    nlinarith only [hh',sq_nonneg ((n:ℝ)-1)]
  have hfailure := ((failure_bound hm1 hVp hτ0 hQ' hVhi haux').trans
    (totalBound_uniform hn1 hτ0 hP')).trans_lt hf
  have hrun : 2 ≤ V*τ/(m:ℝ)^4 := by
    have hm8 : (m:ℝ) ≤ (m:ℝ)^8 := by
      simpa only [pow_one] using pow_le_pow_right₀ hm1 (show 1 ≤ 8 by omega)
    have hdV : (m:ℝ)^8 ≤ V/(m:ℝ)^4 := by
      apply (le_div_iff₀ (pow_pos hmp 4)).mpr
      convert hVlo using 1; ring
    have hVτ : V ≤ V*τ := by nlinarith only [mul_le_mul_of_nonneg_left hτ hVp.le]
    exact (hm.trans hm8).trans (hdV.trans (div_le_div_of_nonneg_right hVτ (pow_nonneg hmp.le 4)))
  exact ⟨hh,steps_le_stop hVp (pow_pos hmp 4) hτ0 hQ' hshort',hdegree,hρ,hspeed,hfailure,steps_half hrun⟩

/-- Regular linear four-uniform extraction with a genuinely growing horizon. -/
theorem eventually_independent (A : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ τ : ℝ, 1 ≤ τ → horizonBudget τ ≤ (n:ℝ) →
      ∀ (α : Type*) [Fintype α] [DecidableEq α],
      (n:ℝ)^24 ≤ (Fintype.card α:ℝ) → (Fintype.card α:ℝ) ≤ (n:ℝ)^(2*A) →
      ∀ H : Finset (Finset α), GreedyLinearDrift.Linear H → (∀ e ∈ H, e.card = 4) →
      (∀ u : α, HypergraphDegreeTrim.degree H u = n^24) →
      ∃ I : Finset α, GreedyHypergraphState.Independent H I ∧
        (Fintype.card α:ℝ)*τ/(2*(n:ℝ)^8) ≤ (I.card:ℝ) := by
  filter_upwards [eventually_uniform_data A] with n hn
  intro τ hτ hbudget α _ _ hVlo hVhi H hlin hfour hregular
  let V : ℝ := Fintype.card α
  have hVlo' : (((n^2:ℕ):ℝ))^12 ≤ V := by simpa only [Nat.cast_pow,← pow_mul] using hVlo
  have hVhi' : V ≤ (((n^2:ℕ):ℝ))^A := by simpa only [Nat.cast_pow,← pow_mul] using hVhi
  have hd := hn τ hτ hbudget V hVlo' hVhi'
  have hreg : ∀ u : α, (HypergraphDegreeTrim.degree H u:ℝ) = (params (n^2) V).d^3 := by
    intro u
    rw [hregular u]
    simp only [params,Nat.cast_pow,← pow_mul]
  have hdegrees : ∀ u : α, HypergraphDegreeTrim.degree H u ≤ (n^2)^12 := by
    intro u
    rw [hregular u,← pow_mul]
  obtain ⟨I,hI,hcard⟩ := independent_of_failure hlin hfour (p := params (n^2) V) rfl hreg
    ((n^2)^12) hdegrees hd.horizon hd.short hd.volume hd.rho_small hd.speed_small hd.failure_small
  refine ⟨I,hI,?_⟩
  rw [hcard]
  simpa only [Nat.cast_pow,← pow_mul] using hd.size_lower

#print axioms totalBound_uniform
#print axioms uniformBound_tendsto
#print axioms eventually_uniform_data
#print axioms eventually_independent
end
end Erdos773.GreedyGrowingFailure
