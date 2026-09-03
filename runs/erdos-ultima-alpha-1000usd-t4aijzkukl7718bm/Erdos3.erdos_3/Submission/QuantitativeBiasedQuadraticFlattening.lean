import Submission.PhaseRefinementBudgets

/-! Quantitative single-phase local quadratic flattening from bias. The rank
increment is <=32/beta^2, the refined radius has an explicit positive lower
bound, and the whole translated inner window remains in the original domain. -/
namespace Erdos3QuantitativeBiasedQuadraticFlattening
open Finset Erdos3PhaseRefinementBudgets Erdos3UnconditionalBiasedPhaseRefinement
  Erdos3BiasedQuadraticBohrRefinement Erdos3LocalQuadraticInverse
  Erdos3CorrelationSifting Erdos3FiniteBohr Erdos3RelativeStableBohr
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- All geometric and precision parameters are numerical. In particular no
inverse theorem, derivative representation, or polarization bound is assumed. -/
theorem quantitative_biased_quadratic_flattening (D : Finset (AddChar G ℂ))
    {R β σ ρ : ℝ} (hR : 0 < R) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hρ : 0 < ρ)
    {o v z w : ℕ} (ho : 0 < o) (hv : 0 < v) (hz : 0 < z) (hw : 0 < w)
    (hst : RelativeStable D o R)
    (hsize : ρ^2 ≤ density (bohr D (relativeWidth D o R/8)))
    (hoB : 1/(o : ℝ) ≤ β/8) (hvB : 1/((v : ℝ)*ρ) ≤ σ*β/16)
    (hzB : 1/(z : ℝ) ≤ σ*β^3/512) (hwB : 1/(w : ℝ) ≤ σ*β/16)
    (q : G → ℂ) (hq : ∀ x, ‖q x‖ = 1)
    (hquad : IsLocallyQuadratic (bohr D R : Set G) q)
    (hbias : β ≤ ‖𝔼 x : bohr D R, q x‖) :
    ∃ E : Finset (AddChar G ℂ), ∃ s t : ℝ, ∃ b ∈ bohr D R,
      (E.card : ℝ) ≤ 32/β^2 ∧ ((D ∪ E).card : ℝ) ≤ D.card+32/β^2 ∧
      baseRadiusLower D.card R o v z ≤ s ∧ stepRadiusLower D.card R σ β o v z w ≤ t ∧
      0 < s ∧ 0 < t ∧
      (∀ x ∈ bohr D s, ∀ y ∈ bohr (D ∪ E) t, (b+x)+y ∈ bohr D R) ∧
      (∀ y ∈ bohr (D ∪ E) t, ‖q (b+y)-q b‖ ≤ σ/2) ∧
      ∀ x ∈ bohr D s, ∀ y ∈ bohr (D ∪ E) t, ‖q ((b+x)+y)-q (b+x)‖ ≤ σ := by
  obtain ⟨hβ',hbudget,herrnum⟩ := refinement_budget_bounds hβ hβ1 hσ hσ1 ho hv hz hw hρ hoB hvB hzB hwB
  have hη : 0 < β/4 := by positivity
  have hε : 0 < β^2/32 := by positivity
  have hε1 : β^2/32 < 1 := by nlinarith
  have heps : β^2/32 ≤ (β/4)^2/2 := by ring_nf; exact le_rfl
  obtain ⟨u,r,s,hgeom,hflat⟩ := exists_unconditional_biased_refinement D hR ho hv hz hw hst hρ hsize
    hη hε hε1 heps hβ' hbudget
  obtain ⟨E,hE,hDE,hqflat⟩ := hflat q hq hquad hbias
  let t := min (relativeWidth D w s/4) (σ*β/16)
  obtain ⟨hs,ht,htr,htz,htw,hsum⟩ := geometry_step_admissible D hR hσ hβ ho hv hz hw hgeom
  obtain ⟨b,hb,hdom,hbase,hall⟩ := hqflat t ht.le htr htz htw hsum
  have hcost := herrnum t (min_le_right _ _)
  have hRank : 2/(β/4)^2 = 32/β^2 := by ring
  rw [hRank] at hE hDE
  refine ⟨E,s,t,b,hb,hE,hDE,geometry_base_lower D hgeom,geometry_step_lower D hgeom,
    hs,ht,hdom,?_,?_⟩
  · intro y hy
    exact (hbase y hy).trans hcost.1
  · intro x hx y hy
    exact (hall x hx y hy).trans hcost.2

#print axioms quantitative_biased_quadratic_flattening
end Erdos3QuantitativeBiasedQuadraticFlattening
