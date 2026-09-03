import Submission.ReducedObservableExtension

/-! A positive-pivot integer phase dependency removes one quadratic
coordinate on a 2n-dilate. The reduced phases stay unit and locally quadratic;
the reduced observable has global [0,1] bounds and an explicit Lipschitz cost. -/
namespace Erdos3RootFreeFactorElimination
open Finset Erdos3ReducedObservableExtension Erdos3RootFreeCoordinateReconstruction
  Erdos3RootFreePhaseStructure Erdos3RootFreeQuadraticDilation
  Erdos3BoundedFrequencyPhaseApproximation Erdos3LocalQuadraticInverse
  Erdos3LocalQuadraticProgressions Erdos3FiniteUniformity Erdos3FiniteFourier
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 6000000

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma remaining_coordinates_card (j : I) :
    Fintype.card {i : I // i ≠ j}+1 = Fintype.card I := by
  have he : Fintype.card {i : I // i ≠ j} = Fintype.card I-1 := by
    simpa using Fintype.card_subtype_compl (fun i : I ↦ i = j)
  have hp : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨j⟩
  omega

lemma reconstructionCost_bound (n B : ℕ) (k : I → ℤ)
    (hn : n ≤ B) (hk : ∀ i, |k i| ≤ B) :
    (reconstructionCost n k : ℝ) ≤ (Fintype.card I+1 : ℕ)*(B : ℝ) := by
  have hcoeff (i : I) : ((k i).natAbs : ℝ) ≤ B := by
    have ht := hk i
    rw [← Int.natCast_natAbs] at ht
    exact_mod_cast ht
  have hs := sum_le_sum (s := univ) (fun i _ ↦ hcoeff i)
  have hnR : (n : ℝ) ≤ B := by exact_mod_cast hn
  simp only [sum_const,card_univ,nsmul_eq_mul] at hs
  simp only [reconstructionCost,NNReal.coe_add,NNReal.coe_sum,NNReal.coe_natCast,
    Nat.cast_add,Nat.cast_one]
  nlinarith

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- The eliminated index set has exactly one fewer element, as proved by
`remaining_coordinates_card`. A positive pivot can be obtained by reversing
the sign of the entire relation if necessary. -/
theorem root_free_factor_elimination (j : I) (n : ℕ) (hn : 0 < n)
    (k : I → ℤ) (hk : k j = n) (Q : I → G → ℂ)
    (hQ : ∀ i x, ‖Q i x‖ = 1) {R S : Set G}
    (hquad : ∀ i, IsLocallyQuadratic R (Q i)) (b : G)
    (hdom : ∀ x ∈ S, ∀ l ≤ 2*n, b+l • x ∈ R)
    (ψ : AddChar G ℂ) {δ γ : ℝ} (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hrel1 : ∀ x ∈ S,
      ‖integerPhase k (fun i ↦ Q i (b+x))-integerPhase k (fun i ↦ Q i b)*ψ x‖ ≤ δ)
    (hrel2 : ∀ x ∈ S,
      ‖integerPhase k (fun i ↦ Q i (b+(2 : ℕ) • x))-
        integerPhase k (fun i ↦ Q i b)*ψ ((2 : ℕ) • x)‖ ≤ δ)
    (hψ : ∀ x ∈ S, ‖ψ x-1‖ ≤ γ)
    (H : (I → ℂ) → ℝ) (hH : ∀ v, 0 ≤ H v ∧ H v ≤ 1)
    {L : NNReal} (hLip : LipschitzWith L H) :
    ∃ P : {i : I // i ≠ j} → G → ℂ, ∃ H' : ({i : I // i ≠ j} → ℂ) → ℝ,
      (∀ i x, ‖P i x‖ = 1) ∧ (∀ i, IsLocallyQuadratic S (P i)) ∧
      (∀ v, 0 ≤ H' v ∧ H' v ≤ 1) ∧ LipschitzWith (L*reconstructionCost n k) H' ∧
      ∀ x ∈ S, |H (fun i ↦ Q i (b+(2*n) • x))-H' (fun i ↦ P i x)| ≤
        (L : ℝ)*(6*(n : ℝ)*δ+2*γ) := by
  let P : {i : I // i ≠ j} → G → ℂ := fun i ↦ rootFreeTransform n (Q i) b
  have hP (i : {i : I // i ≠ j}) (x : G) : ‖P i x‖ = 1 := rootFreeTransform_norm n (Q i) (hQ i) b x
  have hPquad (i : {i : I // i ≠ j}) : IsLocallyQuadratic S (P i) := by
    apply rootFreeTransform_locally_quadratic (hQ i) (hquad i) n b
    · intro x hx
      simpa only [one_nsmul] using hdom x hx 1 (by omega)
    · intro x hx
      exact hdom x hx 2 (by omega)
  obtain ⟨H',hH',hLip',hext⟩ := exists_reduced_observable j n k (fun i ↦ Q i b)
    (fun i ↦ hQ i b) H hH hLip
  refine ⟨P,H',hP,hPquad,hH',hLip',?_⟩
  intro x hx
  let V : I → ℂ := fun i ↦ rootFreeTransform n (Q i) b x
  have hV (i : I) : ‖V i‖ = 1 := rootFreeTransform_norm n (Q i) (hQ i) b x
  have hrel : ‖integerPhase k V-1‖ ≤ 6*(n : ℝ)*δ+2*γ := by
    have ht := rootFreeTransform_linear_error n hn
      (fun y ↦ integerPhase k (fun i ↦ Q i y))
      (fun y ↦ integerPhase_norm k _ (fun i ↦ hQ i y)) ψ b x hδ (hrel1 x hx) (hrel2 x hx)
    rw [rootFreeTransform_integerPhase] at ht
    have hp := (unit_power_oscillation (ψ x) (ψ.norm_apply x) 2).trans
      (mul_le_mul_of_nonneg_left (hψ x hx) (by norm_num : (0 : ℝ) ≤ 2))
    norm_num only [Nat.cast_ofNat] at hp
    exact (norm_sub_le_norm_sub_add_norm_sub (integerPhase k V) ((ψ x)^2) 1).trans (add_le_add ht hp)
  have hvec : ‖(fun i ↦ Q i (b+(2*n) • x))-reconstruct j n k (fun i ↦ Q i b) V‖ ≤
      6*(n : ℝ)*δ+2*γ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    change ‖Q i (b+(2*n) • x)-reconstruct j n k (fun i ↦ Q i b) V i‖ ≤ _
    rw [rootFreeTransform_dilation (hQ i) (hquad i) n b x (hdom x hx)]
    exact reconstruct_error j n k hk (fun i ↦ Q i b) V (fun i ↦ hQ i b) hV (by positivity) hrel i
  rw [hext (fun i ↦ P i x) (fun i ↦ hP i x)]
  change |H (fun i ↦ Q i (b+(2*n) • x))-H (reducedReconstruct j n k (fun i ↦ Q i b) (fun i ↦ V i))| ≤ _
  rw [reconstruct_restrict]
  have hl := hLip.norm_sub_le (fun i ↦ Q i (b+(2*n) • x)) (reconstruct j n k (fun i ↦ Q i b) V)
  rw [Real.norm_eq_abs] at hl
  exact hl.trans (mul_le_mul_of_nonneg_left hvec L.coe_nonneg)

#print axioms remaining_coordinates_card
#print axioms root_free_factor_elimination
end Erdos3RootFreeFactorElimination
