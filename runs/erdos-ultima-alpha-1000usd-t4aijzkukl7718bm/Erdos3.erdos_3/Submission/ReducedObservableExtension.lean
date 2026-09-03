import Submission.RootFreeCoordinateReconstruction
import Submission.ClippedWeakRegularity

/-! Bounded global Lipschitz observables for the reduced phase coordinates.
The algebraic reconstruction need only be Lipschitz on unit tuples; McShane
extension and clipping preserve that restriction and the [0,1] bounds. -/
namespace Erdos3ReducedObservableExtension
open Finset Erdos3RootFreeCoordinateReconstruction Erdos3BoundedFrequencyPhaseApproximation
  Erdos3FiniteCircleGrid Erdos3ClippedWeakRegularity
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def reconstructionCost (n : ℕ) (k : I → ℤ) : NNReal :=
  (n : NNReal)+∑ i : I, ((k i).natAbs : NNReal)

lemma reconstruct_coordinate_distance (j : I) (n : ℕ) (k : I → ℤ) (c v w : I → ℂ)
    (hc : ∀ i, ‖c i‖ = 1) (hv : ∀ i, ‖v i‖ = 1) (hw : ∀ i, ‖w i‖ = 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hvw : ∀ i, ‖v i-w i‖ ≤ δ) (i : I) :
    ‖reconstruct j n k c v i-reconstruct j n k c w i‖ ≤ (reconstructionCost n k : ℝ)*δ := by
  have hcost : (reconstructionCost n k : ℝ) = (n : ℝ)+∑ l : I, ((k l).natAbs : ℝ) := by
    simp only [reconstructionCost,NNReal.coe_add,NNReal.coe_sum,NNReal.coe_natCast]
  have hsum : 0 ≤ ∑ l : I, ((k l).natAbs : ℝ) := sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
  by_cases hi : i = j
  · simp only [reconstruct,if_pos hi,← mul_sub,norm_mul,hc,one_mul]
    have ht := unit_prod_distance (univ.erase j) (fun l ↦ (v l)^(-k l)) (fun l ↦ (w l)^(-k l))
      (fun l _ ↦ by rw [norm_zpow,hv,one_zpow]) (fun l _ ↦ by rw [norm_zpow,hw,one_zpow])
    apply ht.trans
    calc
      _ ≤ ∑ l ∈ univ.erase j, ((k l).natAbs : ℝ)*δ := by
        apply sum_le_sum
        intro l hl
        have hh := (unit_zpow_distance (hv l) (hw l) (-k l)).trans
          (mul_le_mul_of_nonneg_left (hvw l) (Nat.cast_nonneg _))
        simpa only [Int.natAbs_neg] using hh
      _ ≤ ∑ l : I, ((k l).natAbs : ℝ)*δ := sum_le_sum_of_subset_of_nonneg
        (erase_subset _ _) (fun _ _ _ ↦ by positivity)
      _ ≤ _ := by rw [← sum_mul,hcost]; nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  · simp only [reconstruct,if_neg hi,← mul_sub,norm_mul,hc,one_mul]
    have hh := (unit_power_distance (hv i) (hw i) n).trans
      (mul_le_mul_of_nonneg_left (hvw i) (Nat.cast_nonneg n))
    apply hh.trans
    rw [hcost]
    nlinarith

lemma reducedReconstruct_distance (j : I) (n : ℕ) (k : I → ℤ) (c : I → ℂ)
    (hc : ∀ i, ‖c i‖ = 1) (v w : {i : I // i ≠ j} → ℂ)
    (hv : ∀ i, ‖v i‖ = 1) (hw : ∀ i, ‖w i‖ = 1) :
    ‖reducedReconstruct j n k c v-reducedReconstruct j n k c w‖ ≤
      (reconstructionCost n k : ℝ)*‖v-w‖ := by
  have hfill (a : {i : I // i ≠ j} → ℂ) (ha : ∀ i, ‖a i‖ = 1) (i : I) : ‖fillPivot j a i‖ = 1 := by
    by_cases hi : i = j <;> simp [fillPivot,hi,ha]
  have hdist (i : I) : ‖fillPivot j v i-fillPivot j w i‖ ≤ ‖v-w‖ := by
    by_cases hi : i = j
    · simp only [fillPivot,dif_pos hi,sub_self,norm_zero]
      exact norm_nonneg _
    · simp only [fillPivot,dif_neg hi]
      exact norm_le_pi_norm (v-w) ⟨i,hi⟩
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  exact reconstruct_coordinate_distance j n k c (fillPivot j v) (fillPivot j w)
    hc (hfill v hv) (hfill w hw) (norm_nonneg _) hdist i

/-- A bounded Lipschitz observable of the original coordinates admits a
bounded global Lipschitz reduced observable, agreeing with reconstruction
on every unit tuple. -/
theorem exists_reduced_observable (j : I) (n : ℕ) (k : I → ℤ) (c : I → ℂ)
    (hc : ∀ i, ‖c i‖ = 1) (H : (I → ℂ) → ℝ)
    (hH : ∀ v, 0 ≤ H v ∧ H v ≤ 1) {L : NNReal} (hLip : LipschitzWith L H) :
    ∃ H' : ({i : I // i ≠ j} → ℂ) → ℝ,
      (∀ v, 0 ≤ H' v ∧ H' v ≤ 1) ∧
      LipschitzWith (L*reconstructionCost n k) H' ∧
      ∀ v, (∀ i, ‖v i‖ = 1) → H' v = H (reducedReconstruct j n k c v) := by
  let S : Set ({i : I // i ≠ j} → ℂ) := {v | ∀ i, ‖v i‖ = 1}
  let f := fun v ↦ H (reducedReconstruct j n k c v)
  have hlocal : LipschitzOnWith (L*reconstructionCost n k) f S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro v hv w hw
    have hh := hLip.dist_le_mul (reducedReconstruct j n k c v) (reducedReconstruct j n k c w)
    have hr := reducedReconstruct_distance j n k c hc v w hv hw
    dsimp only [f]
    rw [dist_eq_norm] at hh
    apply hh.trans
    simpa only [NNReal.coe_mul,mul_assoc,dist_eq_norm] using
      mul_le_mul_of_nonneg_left hr L.coe_nonneg
  obtain ⟨g,hg,heq⟩ := hlocal.extend_real
  refine ⟨fun v ↦ clip01 (g v),fun v ↦ clip01_bounds _,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [Real.dist_eq]
    exact (clip01_abs_sub (g v) (g w)).trans (by simpa only [Real.dist_eq] using hg.dist_le_mul v w)
  · intro v hv
    change clip01 (g v) = H (reducedReconstruct j n k c v)
    rw [← heq hv]
    dsimp only [clip01,f]
    rw [min_eq_right (hH _).2,max_eq_right (hH _).1]

#print axioms reducedReconstruct_distance
#print axioms exists_reduced_observable
end Erdos3ReducedObservableExtension
