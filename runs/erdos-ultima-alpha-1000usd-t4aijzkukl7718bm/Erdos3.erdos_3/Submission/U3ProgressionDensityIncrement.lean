import Submission.ProgressionIncrementParameters
import Submission.VariableRadiusQuadraticInverse
import Submission.NormalizedQuadraticDensityIncrement

/-! A global U³-to-proper-progression density increment with an explicit
modulus threshold. This is not a higher-order or summability theorem. -/
namespace Erdos3U3ProgressionDensityIncrement
open Finset Erdos3ProgressionIncrementParameters Erdos3QuadraticCorrelationProgressionIncrement
  Erdos3VariableRadiusQuadraticInverse Erdos3NormalizedQuadraticInverse
  Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3CorrelationSifting
  Erdos3InteriorQuadraticDensityIncrement
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

/-- Large U³ of a centered one-bounded function gives a positive mean on a
proper length-L progression. All size costs depend only on delta, r, and L. -/
theorem U3_progression_increment (p : ℕ) [NeZero p]
    (h2 : Function.Bijective (fun x : ZMod p ↦ x+x)) (f : ZMod p → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hf0 : 𝔼 x, f x = 0) {δ r : ℝ}
    (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 (fun x ↦ (f x : ℂ)))
    (hr : 0 < r) (hrcorr : r ≤ normalizedCorrelation δ) (L : ℕ) (hL : 0 < L)
    (hp : incrementThreshold (normalizedRank δ) L r ≤ p) :
    ∃ a : ZMod p, ∃ d : ℕ, 0 < d ∧
      d ≤ partitionStride (normalizedRank δ) (incrementLinearMesh L r)
        (incrementCoarseMesh (normalizedRank δ) L r) (incrementAccuracy L r) ∧
      Function.Injective (fun j : Fin L ↦ a+j.val • (d : ZMod p)) ∧
      r/16 ≤ 𝔼 j : Fin L, f (a+j.val • (d : ZMod p)) := by
  have hf' (x : ZMod p) : ‖(f x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hf x
  obtain ⟨C,R,q,hC,hR,hRmax,hstable,hq,hquad,hcorr⟩ :=
    stable_radius_local_quadratic_inverse h2 (fun x ↦ (f x : ℂ)) hf' hδ hU (incrementPrecision_pos r)
  obtain ⟨a,d,hd,hdb,hproper,hinc⟩ := quadratic_correlation_progression_increment p C hR
    (by linarith : R ≤ 1/16) (incrementPrecision_pos r) hstable f hf hf0 q hq hquad hr
    (hrcorr.trans hcorr)
    (incrementCoarseLength L r) (incrementLocalLength L r) L (incrementLinearMesh L r)
    (incrementCoarseMesh (normalizedRank δ) L r) (incrementAccuracy L r)
    (incrementCoarseLength_pos L r) (incrementLocalLength_pos L r) hL (incrementLinearMesh_pos L r)
    (incrementCoarseMesh_pos (normalizedRank δ) L r)
    (increment_bohr_mesh C hC L r hR) (increment_partition_budget hC hr hp)
  refine ⟨a,d,hd,hdb.trans ?_,hproper,hinc⟩
  unfold partitionStride
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 2 hC)

/-- A density increment on a genuine arithmetic progression, not merely on
an unstructured local phase cell. The modulus threshold is explicit. -/
theorem U3_progression_density_increment (p : ℕ) [NeZero p]
    (h2 : Function.Bijective (fun x : ZMod p ↦ x+x)) (A : Finset (ZMod p)) {δ r : ℝ}
    (hδ : 0 < δ)
    (hU : δ ≤ uniformityPower 2 (fun x ↦ ((indicator A x-density A : ℝ) : ℂ)))
    (hr : 0 < r) (hrcorr : r ≤ normalizedCorrelation δ) (L : ℕ) (hL : 0 < L)
    (hp : incrementThreshold (normalizedRank δ) L r ≤ p) :
    ∃ a : ZMod p, ∃ d : ℕ, 0 < d ∧
      d ≤ partitionStride (normalizedRank δ) (incrementLinearMesh L r)
        (incrementCoarseMesh (normalizedRank δ) L r) (incrementAccuracy L r) ∧
      Function.Injective (fun j : Fin L ↦ a+j.val • (d : ZMod p)) ∧
      density A+r/16 ≤ 𝔼 j : Fin L, indicator A (a+j.val • (d : ZMod p)) := by
  letI : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  let f : ZMod p → ℝ := fun x ↦ indicator A x-density A
  have hf0 : (𝔼 x, f x) = 0 := by
    simp only [f,expect_sub_distrib,expect_indicator,Fintype.expect_const,sub_self]
  obtain ⟨a,d,hd,hbound,hproper,hinc⟩ := U3_progression_increment p h2 f
    (centered_indicator_bound A) hf0 hδ hU hr hrcorr L hL hp
  change r/16 ≤ 𝔼 j : Fin L, (indicator A (a+j.val • (d : ZMod p))-density A) at hinc
  rw [expect_sub_distrib,Fintype.expect_const] at hinc
  exact ⟨a,d,hd,hbound,hproper,by linarith⟩

#print axioms U3_progression_increment
#print axioms U3_progression_density_increment
end Erdos3U3ProgressionDensityIncrement
