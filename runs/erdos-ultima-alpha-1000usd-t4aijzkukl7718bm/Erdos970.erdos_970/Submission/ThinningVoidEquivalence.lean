import Submission.FiniteThinningGeneral
import Submission.SoftEndpointHazardLimit

/-! Exact consequences of the auxiliary void hypotheses under finite prime
thinning. These equivalences do not assert either hypothesis. -/
namespace Erdos970.GapAverages
open Finset Real Filter
open scoped Topology
set_option maxHeartbeats 2000000

lemma tendsto_of_abs_sub_le_inv {f : ℕ → ℝ} {a : ℝ}
    (h : ∀ n, |f n-a| ≤ 1/((n : ℝ)+1)) : Tendsto f atTop (𝓝 a) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
    (Eventually.of_forall h) tendsto_one_div_add_atTop_nhds_zero_nat

/-- Genuine prime sets tending to the independent-thinning model, both in
void mass and in density. No independence of the original positions is used. -/
theorem exists_padding_limits (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (t : ℝ) (ht : 0 < t) (M : ℕ) :
    ∃ R : ℕ → Finset ℕ,
      (∀ n, Disjoint P (R n) ∧ ∀ p ∈ R n, p.Prime ∧ M ≤ p) ∧
      Tendsto (fun n => density (P ∪ R n)) atTop (𝓝 (density P*(1-exp (-t)))) ∧
      ∀ m ≤ M, Tendsto (fun n => coveredFraction (P ∪ R n) m) atTop
        (𝓝 (countLaplace P t m)) := by
  have h (n : ℕ) := FiniteThinning.exists_padding_approx_general P hP t ht M
    (1/((n : ℝ)+1)) (by positivity)
  choose R hdis hprime hd hcount using h
  refine ⟨R,fun n => ⟨hdis n,hprime n⟩,tendsto_of_abs_sub_le_inv (fun n => (hd n).le),?_⟩
  intro m hm
  exact tendsto_of_abs_sub_le_inv (fun n => (hcount n m hm).le)

/-- The universal exponential void hypothesis is equivalent to Poisson-form
Laplace domination at every positive parameter, with the same constant. -/
theorem exponential_void_iff_laplace (c : ℝ) :
    ExponentialVoidBound c ↔
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ t : ℝ, 0 < t → ∀ m : ℕ,
        countLaplace P t m ≤ exp (-(c*(m : ℝ)*density P*(1-exp (-t)))) := by
  constructor
  · intro h P hP t ht m
    obtain ⟨R,hR,hd,hv⟩ := exists_padding_limits P hP t ht m
    have hlim := (Real.continuous_exp.tendsto _).comp (hd.const_mul (c*(m : ℝ))).neg
    have he : Tendsto (fun n => exp (-(c*(m : ℝ)*density (P ∪ R n)))) atTop
        (𝓝 (exp (-(c*(m : ℝ)*density P*(1-exp (-t)))))) := by
      simpa only [mul_assoc] using hlim
    apply le_of_tendsto_of_tendsto (hv m le_rfl) he
    apply Eventually.of_forall
    intro n
    exact h (P ∪ R n) (fun p hp => (mem_union.mp hp).elim (hP p) (fun hp => (hR n).2 p hp |>.1)) m
  · intro h P hP m
    have hd : Tendsto (fun t : ℝ => 1-exp (-t)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub tendsto_exp_neg_atTop_nhds_zero
    have he : Tendsto (fun t : ℝ => exp (-(c*(m : ℝ)*density P*(1-exp (-t))))) atTop
        (𝓝 (exp (-(c*(m : ℝ)*density P)))) := by
      simpa only [mul_one] using (Real.continuous_exp.tendsto _).comp (hd.const_mul (c*(m : ℝ)*density P)).neg
    apply le_of_tendsto_of_tendsto (countLaplace_tendsto_void P m) he
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact h P hP t ht m

/-- The analogous binomial-form equivalence for the stronger geometric
candidate, also retained as an explicit hypothesis. -/
theorem geometric_void_iff_laplace :
    GeometricVoidBound ↔
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ t : ℝ, 0 < t → ∀ m : ℕ,
        countLaplace P t m ≤ (1-density P*(1-exp (-t)))^m := by
  constructor
  · intro h P hP t ht m
    obtain ⟨R,hR,hd,hv⟩ := exists_padding_limits P hP t ht m
    have he : Tendsto (fun n => (1-density (P ∪ R n))^m) atTop
        (𝓝 ((1-density P*(1-exp (-t)))^m)) := (tendsto_const_nhds.sub hd).pow m
    apply le_of_tendsto_of_tendsto (hv m le_rfl) he
    apply Eventually.of_forall
    intro n
    exact h (P ∪ R n) (fun p hp => (mem_union.mp hp).elim (hP p) (fun hp => (hR n).2 p hp |>.1)) m
  · intro h P hP m
    have hd : Tendsto (fun t : ℝ => 1-exp (-t)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [sub_zero] using tendsto_const_nhds.sub tendsto_exp_neg_atTop_nhds_zero
    have he : Tendsto (fun t : ℝ => (1-density P*(1-exp (-t)))^m) atTop
        (𝓝 ((1-density P)^m)) := by
      simpa only [mul_one] using (tendsto_const_nhds.sub (hd.const_mul (density P))).pow m
    apply le_of_tendsto_of_tendsto (countLaplace_tendsto_void P m) he
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact h P hP t ht m

#print axioms exists_padding_limits
#print axioms exponential_void_iff_laplace
#print axioms geometric_void_iff_laplace
end Erdos970.GapAverages
