import Submission.OrientedPhaseDependency

/-! A nonzero bounded-integer quadratic dependency removes one coordinate
on an ordinary translated Bohr window. Dilation is transported through an
additive equivalence; no root branches or extra quadratic coordinates remain.
This is a local dimension-reduction step, not yet a density increment. -/
namespace Erdos3LocalFactorDimensionReduction
open Finset Erdos3OrientedPhaseDependency Erdos3BohrFactorCoordinateElimination
  Erdos3ReducedObservableExtension Erdos3RootFreePhaseStructure
  Erdos3BoundedFrequencyPhaseApproximation Erdos3LocalQuadraticInverse
  Erdos3StableMaskedUniformity Erdos3FiniteUniformity Erdos3FiniteBohr
  Erdos3BohrTransport Erdos3RelativeStableBohr Erdos3CorrelationSifting
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 6000000

variable {G I : Type*} [AddCommGroup G] [Fintype G] [Fintype I] [DecidableEq I]

/-- One local factor coordinate is removed. The new phase index type has
cardinality |I|-1, the rank grows by <=32/beta^2+1, and the radius lower bound
is explicit. The required dilation is invertible, for example, in a prime
cyclic group whose order is larger than twice the pivot coefficient. -/
theorem local_factor_dimension_reduction (D : Finset (AddChar G ℂ))
    {R β τ : ℝ} (hR : 0 < R) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) {o : ℕ} (ho : 0 < o)
    (hst : RelativeStable D o R) (hoB : 1/(o : ℝ) ≤ β/8)
    (j : I) (k : I → ℤ) (hj : k j ≠ 0)
    (hdil : Function.Bijective (fun x : G ↦ (2*(k j).natAbs) • x))
    (Q : I → G → ℂ) (hQ : ∀ i x, ‖Q i x‖ = 1)
    (hquad : ∀ i, IsLocallyQuadratic (bohr D R : Set G) (Q i))
    (hU : β^2*(density (bohr D R))^3 ≤
      uniformityPower 1 (mask (bohr D R) (fun x ↦ integerPhase k (fun i ↦ Q i x))))
    (H : (I → ℂ) → ℝ) (hH : ∀ v, 0 ≤ H v ∧ H v ≤ 1)
    {L : NNReal} (hLip : LipschitzWith L H) :
    ∃ C : Finset (AddChar G ℂ), ∃ u : ℝ, ∃ b ∈ bohr D R,
      ∃ P : {i : I // i ≠ j} → G → ℂ, ∃ H' : ({i : I // i ≠ j} → ℂ) → ℝ,
        (C.card : ℝ) ≤ D.card+32/β^2+1 ∧
        eliminationRadius D.card R τ β o (k j).natAbs ≤ u ∧ 0 < u ∧
        (∀ x ∈ bohr C u, b+x ∈ bohr D R) ∧
        (∀ i x, ‖P i x‖ = 1) ∧ (∀ i, IsLocallyQuadratic (bohr C u : Set G) (P i)) ∧
        (∀ v, 0 ≤ H' v ∧ H' v ≤ 1) ∧
        LipschitzWith (L*reconstructionCost (k j).natAbs k) H' ∧
        ∀ x ∈ bohr C u, |H (fun i ↦ Q i (b+x))-H' (fun i ↦ P i x)| ≤ (L : ℝ)*τ := by
  let n := (k j).natAbs
  have hn : 0 < n := Int.natAbs_pos.mpr hj
  obtain ⟨l,hl,_,hcost,hUl⟩ := exists_positive_pivot k j hj Q hQ (bohr D R)
  have hU' : β^2*(density (bohr D R))^3 ≤
      uniformityPower 1 (mask (bohr D R) (fun x ↦ integerPhase l (fun i ↦ Q i x))) := by
    rw [hUl]
    exact hU
  obtain ⟨C,u,b,hb,P,H',hC,hrad,hu,hdom,hP,hPquad,hH',hLip',herr⟩ :=
    bohr_factor_elimination_positive_pivot D hR hβ hβ1 hτ hτ1 ho hst hoB
      j n hn l hl Q hQ hquad hU' H hH hLip
  let e : G ≃+ G := AddEquiv.ofBijective (nsmulAddMonoidHom (2*n)) hdil
  have hinv (x : G) (hx : x ∈ bohr (transportChars e C) u) : e.symm x ∈ bohr C u := by
    rw [← transport_bohr] at hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    simpa only [e.symm_apply_apply] using hy
  have he (x : G) : (2*n) • e.symm x = x := e.apply_symm_apply x
  let P' : {i : I // i ≠ j} → G → ℂ := fun i x ↦ P i (e.symm x)
  have hP' (i : {i : I // i ≠ j}) (x : G) : ‖P' i x‖ = 1 := hP i _
  have hquad' (i : {i : I // i ≠ j}) : IsLocallyQuadratic (bohr (transportChars e C) u : Set G) (P' i) := by
    have ht := Erdos3RootFreePhaseStructure.IsLocallyQuadratic.comp_affine (hPquad i)
      e.symm.toAddMonoidHom 0 (fun x hx ↦ by simpa only [zero_add] using hinv x hx)
    simpa only [zero_add] using ht
  rw [hcost n] at hLip'
  refine ⟨transportChars e C,u,b,hb,P',H',?_,hrad,hu,?_,hP',hquad',hH',hLip',?_⟩
  · simpa only [transportChars_card] using hC
  · intro x hx
    have ht := hdom (e.symm x) (hinv x hx)
    rwa [he] at ht
  · intro x hx
    have ht := herr (e.symm x) (hinv x hx)
    rw [he] at ht
    exact ht

#print axioms local_factor_dimension_reduction
end Erdos3LocalFactorDimensionReduction
