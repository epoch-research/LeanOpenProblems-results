import Submission.ExpPowerDominanceExplore

/-! A hypothetical witness has no nonzero polynomial relation between the
distance to the boundary and its indicator generating function. This is a
necessary transcendence property, not a contradiction for Boolean series. -/
namespace Erdos66LogBoundaryPolynomial
open Filter AdditiveCombinatorics Erdos66Generating Erdos66ExpPowerDominance
open scoped Topology Classical
set_option maxHeartbeats 1800000

lemma exponential_parameter :
    Tendsto (fun x : ℝ ↦ Real.exp (-x)) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot,?_⟩
  exact Eventually.of_forall (fun x ↦ Real.exp_pos (-x))

lemma kernel_normalization (F x : ℝ) :
    F*Real.sqrt (Real.exp (-x)/(-Real.log (Real.exp (-x))))=
      F/model (1/2) (1/2) x := by
  rw [Real.log_exp,neg_neg,Real.sqrt_div (Real.exp_pos _).le]
  simp only [Real.sqrt_eq_rpow,←Real.exp_mul,model]
  rw [show -x*(1/2)=-(1/2*x) by ring,Real.exp_neg]
  ring

lemma witness_exponential_profile {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun x ↦ series (indicator A) (1-Real.exp (-x))/model (1/2) (1/2) x)
      atTop (𝓝 (Real.sqrt c)) := by
  have hh := (witness_generating_limit_zero h).comp exponential_parameter
  apply hh.congr
  intro x
  exact kernel_normalization _ _

/-- Every nonzero finite bivariate polynomial is eventually nonzero when
evaluated at (1-r,F_A(r)), where F_A is the indicator generating function. -/
theorem witness_polynomial_eventually_ne_zero {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (S : Finset (ℕ×ℕ)) (hS : S.Nonempty) (a : ℕ×ℕ → ℝ) (ha : ∀ p∈S, a p≠0) :
    ∀ᶠ r in 𝓝[<] 1, (∑ p∈S, a p*((1-r)^p.1*series (indicator A) r^p.2))≠0 := by
  have hcpos := Erdos66Explore.limit_pos hc h
  have hh := polynomial_eventually_ne_zero (Real.sqrt_pos.mpr hcpos).ne'
    (witness_exponential_profile h) S hS a ha
  filter_upwards [negative_log_one_sub.eventually hh,unit_interval_eventually] with r hr hr01
  have he : Real.exp (-(-Real.log (1-r)))=1-r := by
    rw [neg_neg,Real.exp_log (sub_pos.mpr hr01.2)]
  simpa only [monomial,he,sub_sub_cancel] using hr

/-- In particular no fixed nonzero polynomial identity can hold on a whole
left-neighborhood of the convergence boundary. -/
theorem witness_no_polynomial_identity {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ¬∃ (S : Finset (ℕ×ℕ)) (a : ℕ×ℕ → ℝ), S.Nonempty ∧ (∀ p∈S, a p≠0) ∧
      ∀ᶠ r in 𝓝[<] 1, (∑ p∈S, a p*((1-r)^p.1*series (indicator A) r^p.2))=0 := by
  rintro ⟨S,a,hS,ha,he⟩
  obtain ⟨r,hr,hne⟩ := (he.and (witness_polynomial_eventually_ne_zero hc h S hS a ha)).exists
  exact hne hr

end Erdos66LogBoundaryPolynomial
