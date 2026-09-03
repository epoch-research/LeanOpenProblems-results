import Submission.BooleanKernelDuality
import Submission.BooleanKernelUniversal

/-! The exact Boolean-cost kernel class is equivalent to the class of all
normalized nonnegative Boolean upper polynomials. No size restriction is imposed. -/
namespace Erdos970.FiniteSelberg
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma booleanValue_at_subset (a : Finset ι → ℝ) (T : Finset ι) :
    booleanValue a (fun i => decide (i ∈ T)) = ∑ Q ∈ T.powerset, a Q := by
  unfold booleanValue
  simp only [hitMonomial_eq, decide_eq_true_eq, ← subset_iff, mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  congr 1
  ext Q
  simp

/-- Multilinear coefficients are uniquely determined by the values on the cube. -/
theorem booleanValue_injective : Function.Injective (booleanValue (ι := ι)) := by
  intro a b hab
  have hsum (T : Finset ι) : (∑ Q ∈ T.powerset, (a Q - b Q)) = 0 := by
    rw [sum_sub_distrib, ← booleanValue_at_subset a T, ← booleanValue_at_subset b T, hab, sub_self]
  funext T
  induction T using Finset.strongInductionOn
  rename_i T ih
  have he : (∑ Q ∈ T.powerset, (a Q - b Q)) = a T - b T := by
    apply sum_eq_single T
    · intro Q hQ hQT
      have hs : Q ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp hQ, hQT⟩
      rw [ih Q hs, sub_self]
    · simp
  have hz := hsum T
  rw [he] at hz
  exact sub_eq_zero.mp hz

/-- Any admissible upper polynomial has exactly the coefficients of a normalized
squared kernel, not just the same values or a larger coefficient cost. -/
theorem upperWeight_is_normalized_square (q : ι → ℝ)
    (hq : ∀ i, 0 < q i ∧ q i < 1) (a : Finset ι → ℝ)
    (ha : ∀ ω, 0 ≤ booleanValue a ω) (h0 : booleanValue a (fun _ => false) = 1) :
    ∃ c : Finset ι → ℝ, (∑ Q : Finset ι, c Q) = 1 ∧
      booleanSquareCoefficient (ordinaryCoefficient q c) = a := by
  obtain ⟨c, hc, he⟩ := exists_normalized_square_kernel q hq (booleanValue a) ha h0
  refine ⟨c, hc, booleanValue_injective ?_⟩
  funext ω
  rw [booleanValue_square, he]

/-- Every nonnegative normalized upper weight is attained with exactly its
original objective by an unrestricted signed orthogonal kernel. -/
theorem upperWeight_objective_attained (q : ι → ℝ)
    (hq : ∀ i, 0 < q i ∧ q i < 1) (X : ℝ) (a : Finset ι → ℝ)
    (ha : ∀ ω, 0 ≤ booleanValue a ω) (h0 : booleanValue a (fun _ => false) = 1) :
    ∃ c : Finset ι → ℝ, (∑ Q : Finset ι, c Q) = 1 ∧
      booleanKernelObjective q X c = booleanObjective q X a := by
  obtain ⟨c, hc, he⟩ := upperWeight_is_normalized_square q hq a ha h0
  refine ⟨c, hc, ?_⟩
  rw [← booleanObjective_square, he]

#print axioms booleanValue_injective
#print axioms upperWeight_objective_attained
end Erdos970.FiniteSelberg
