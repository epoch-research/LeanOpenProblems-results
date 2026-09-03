import FormalConjecturesUtil
import Submission.LocalEdgeMarginals
import Submission.PolynomialRateCriterion

/-! Fixed bounded-query edge marginals have a quadratic objective even
when the actual graph extremal number has a subquadratic pure-power
asymptotic. This is only an obstruction to bounded-query consistency;
it makes no assertion about globally positive moment relaxations. -/
open Filter Asymptotics SimpleGraph
open scoped Classical Topology
namespace Erdos713LocalEdgeMarginalsAsymptotic
open Erdos713LocalEdgeMarginals
set_option maxHeartbeats 1000000

lemma higher_power_ratio {f : ℕ → ℝ} {α β c : ℝ} (hαβ : α < β)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    Tendsto (fun n : ℕ => f n/(n : ℝ)^β) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun n : ℕ => (n : ℝ)^(α-β)) atTop (𝓝 0) := by
    simpa only [neg_sub] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hαβ)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hprod := (Erdos713PolynomialRate.ratio_limit hf).mul hsmall
  rw [mul_zero] at hprod
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_sub hnR]
  field_simp [(Real.rpow_pos_of_pos hnR α).ne']

lemma quadratic_lower {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (hn : 2 ≤ n) :
    p/4*(n : ℝ)^2 ≤ objective p (⊤ : SimpleGraph (Fin n)).edgeFinset := by
  rw [graph_objective]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [mul_nonneg hp (mul_nonneg (by linarith : (0 : ℝ) ≤ n)
    (by linarith : (0 : ℝ) ≤ (n : ℝ)-2))]

/-- For every fixed query budget and multiplicative factor, these locally
positive coherent functionals eventually exceed that factor times a
subquadratic pure-power sequence. -/
theorem objective_gap {f : ℕ → ℝ} {α c : ℝ} (hα : α < 2)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) (r : ℕ) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, K*f n <
      objective (density r) (⊤ : SimpleGraph (Fin n)).edgeFinset := by
  have hlim : Tendsto (fun n : ℕ => K*f n/(n : ℝ)^2) atTop (𝓝 0) := by
    have hh := (higher_power_ratio hα hf).const_mul K
    simpa only [mul_zero, Real.rpow_two, mul_div_assoc] using hh
  have hp := density_pos r
  filter_upwards [hlim.eventually_lt_const (show 0 < density r/4 by positivity),
    eventually_ge_atTop (2 : ℕ)] with n hsmall hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact ((div_lt_iff₀ (sq_pos_of_pos hnR)).mp hsmall).trans_le (quadratic_lower hp.le hn)

/-- Graph-extremal specialization; no positivity, normalization, or
coherence condition is being inferred for queries larger than r. -/
theorem extremal_objective_gap {W : Type*} (H : SimpleGraph W) {α c : ℝ}
    (hα : α < 2)
    (hf : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n : ℕ => c*(n : ℝ)^α)) (r : ℕ) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, K*(extremalNumber n H : ℝ) <
      objective (density r) (⊤ : SimpleGraph (Fin n)).edgeFinset :=
  objective_gap hα hf r K

#print axioms higher_power_ratio
#print axioms quadratic_lower
#print axioms objective_gap
#print axioms extremal_objective_gap
end Erdos713LocalEdgeMarginalsAsymptotic
