import Submission.BohrFactorCoordinateElimination

/-! Orienting a nonzero integer dependency to a positive pivot preserves
all coefficient sizes, reconstruction costs, and masked uniformity powers. -/
namespace Erdos3OrientedPhaseDependency
open Finset Erdos3RootFreePhaseStructure Erdos3BoundedFrequencyPhaseApproximation
  Erdos3ReducedObservableExtension Erdos3FiniteUniformity Erdos3FiniteFourier
  Erdos3StableMaskedUniformity
open scoped BigOperators Classical ComplexConjugate
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma uniformityPower_conj (n : ℕ) (f : G → ℂ) :
    uniformityPower n (fun x ↦ conj (f x)) = uniformityPower n f := by
  induction n generalizing f with
  | zero => simp only [uniformityPower,← expect_conj,Complex.norm_conj]
  | succ n ih =>
    simp only [uniformityPower,derivative_conj_fun,ih]

lemma mask_conj (W : Finset G) (f : G → ℂ) :
    mask W (fun x ↦ conj (f x)) = fun x ↦ conj (mask W f x) := by
  funext x
  by_cases hx : x ∈ W <;> simp only [mask,hx,if_true,if_false,map_zero]

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma integerPhase_neg (k : I → ℤ) (v : I → ℂ) (hv : ∀ i, ‖v i‖ = 1) :
    integerPhase (fun i ↦ -k i) v = conj (integerPhase k v) := by
  simp only [integerPhase,map_prod]
  apply prod_congr rfl
  intro i hi
  rw [zpow_neg]
  symm
  exact eq_inv_of_mul_eq_one_right (mul_conj_eq_one (by rw [norm_zpow,hv,one_zpow]))

/-- A nonzero pivot is made positive by conjugating the whole relation when
necessary. No new frequency growth or uniformity loss is incurred. -/
theorem exists_positive_pivot (k : I → ℤ) (j : I) (hj : k j ≠ 0)
    (Q : I → G → ℂ) (hQ : ∀ i x, ‖Q i x‖ = 1) (W : Finset G) :
    ∃ l : I → ℤ, l j = ((k j).natAbs : ℤ) ∧
      (∀ i, |l i| = |k i|) ∧
      (∀ n, reconstructionCost n l = reconstructionCost n k) ∧
      uniformityPower 1 (mask W (fun x ↦ integerPhase l (fun i ↦ Q i x))) =
        uniformityPower 1 (mask W (fun x ↦ integerPhase k (fun i ↦ Q i x))) := by
  by_cases hp : 0 < k j
  · refine ⟨k,?_,fun i ↦ rfl,fun n ↦ rfl,rfl⟩
    rw [Int.natCast_natAbs,abs_of_pos hp]
  · have hn : k j < 0 := lt_of_le_of_ne (le_of_not_gt hp) hj
    refine ⟨fun i ↦ -k i,?_,fun i ↦ abs_neg _,?_,?_⟩
    · rw [Int.natCast_natAbs,abs_of_neg hn]
    · intro n
      simp only [reconstructionCost,Int.natAbs_neg]
    · have he : (fun x ↦ integerPhase (fun i ↦ -k i) (fun i ↦ Q i x)) =
          fun x ↦ conj (integerPhase k (fun i ↦ Q i x)) := by
        funext x
        exact integerPhase_neg k _ (fun i ↦ hQ i x)
      rw [he,mask_conj,uniformityPower_conj]

#print axioms exists_positive_pivot
end Erdos3OrientedPhaseDependency
