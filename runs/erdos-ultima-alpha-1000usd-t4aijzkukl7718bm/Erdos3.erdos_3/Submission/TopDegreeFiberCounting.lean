import Submission.GradedPolynomialModel
import Submission.EvenPolynomialModel

/-! In a mixed-degree model, the highest even-degree component can be counted
by its paired energy rather than frozen to a diagonal slice. Only the lower
coefficient space contributes to the denominator. This remains a model theorem. -/
namespace Erdos3TopDegreeFiberCounting
open Finset Erdos3FiniteSamplingMoments Erdos3EvenPolynomialModel
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {H Q C : Type*} [Fintype H] [Nonempty H]
variable [AddCommGroup Q] [Fintype Q] [Fintype C] [Zero C]

lemma zero_slice_le_expect (g : C → ℝ) (hg : ∀ c, 0 ≤ g c) :
    g 0/(Fintype.card C : ℝ) ≤ 𝔼 c : C, g c := by
  rw [Fintype.expect_eq_sum_div_card]
  exact div_le_div_of_nonneg_right (single_le_sum (fun c _ ↦ hg c) (mem_univ 0)) (Nat.cast_nonneg _)

noncomputable def fiberedEvenCount (m : ℕ) (M : H → C → Fin (2*m+2) → H)
    (f : H → Q → ℝ) : ℝ :=
  𝔼 a : H, 𝔼 c : C, 𝔼 p : Q × (Fin m → Q) × (Fin m → Q),
    ∏ j : Fin (2*m+2), f (M a c j) (evenPolynomial m p j.val)

/-- The top even degree has no coefficient-cardinality cost. The lower
component M is arbitrary except that its zero coefficient slice is constant. -/
theorem fiberedEvenCount_lower (m : ℕ) (M : H → C → Fin (2*m+2) → H)
    (hM : ∀ a j, M a 0 j = a) (f : H → Q → ℝ) (hf : ∀ a z, 0 ≤ f a z) :
    (𝔼 a : H, 𝔼 z : Q, f a z)^(2*m+2)/(Fintype.card C : ℝ) ≤ fiberedEvenCount m M f := by
  have hpow : (𝔼 a : H, 𝔼 z : Q, f a z)^(2*m+2) ≤
      𝔼 a : H, (𝔼 z : Q, f a z)^(2*m+2) :=
    expect_even_pow_le (show Even (2*m+2) from ⟨m+1,by omega⟩) (fun a ↦ 𝔼 z : Q, f a z)
  have hpoint (a : H) : (𝔼 z : Q, f a z)^(2*m+2)/(Fintype.card C : ℝ) ≤
      𝔼 c : C, 𝔼 p : Q × (Fin m → Q) × (Fin m → Q),
        ∏ j : Fin (2*m+2), f (M a c j) (evenPolynomial m p j.val) := by
    have hzero := zero_slice_le_expect
      (fun c : C ↦ 𝔼 p : Q × (Fin m → Q) × (Fin m → Q),
        ∏ j : Fin (2*m+2), f (M a c j) (evenPolynomial m p j.val))
      (fun c ↦ expect_nonneg (fun p _ ↦ prod_nonneg (fun j _ ↦ hf _ _)))
    simp only [hM] at hzero
    exact (div_le_div_of_nonneg_right (even_polynomial_model_lower m (f a))
      (Nat.cast_nonneg _)).trans hzero
  calc
    _ ≤ (𝔼 a : H, (𝔼 z : Q, f a z)^(2*m+2))/(Fintype.card C : ℝ) :=
      div_le_div_of_nonneg_right hpow (Nat.cast_nonneg _)
    _ = 𝔼 a : H, (𝔼 z : Q, f a z)^(2*m+2)/(Fintype.card C : ℝ) := expect_div _ _ _
    _ ≤ _ := expect_le_expect (fun a _ ↦ hpoint a)

/-- Product-space form of the mean. -/
theorem fiberedEvenCount_lower_product (m : ℕ) (M : H → C → Fin (2*m+2) → H)
    (hM : ∀ a j, M a 0 j = a) (f : H × Q → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (𝔼 a : H × Q, f a)^(2*m+2)/(Fintype.card C : ℝ) ≤
      fiberedEvenCount m M (fun a z ↦ f (a,z)) := by
  rw [show (𝔼 a : H × Q, f a) = 𝔼 a : H, 𝔼 z : Q, f (a,z) from expect_product _ _ _]
  exact fiberedEvenCount_lower m M hM (fun a z ↦ f (a,z)) (fun a z ↦ hf (a,z))

section Graded
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {G : I → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)]
open Erdos3GradedPolynomialModel

/-- In particular, for a graded lower factor and arbitrary top-degree Q, the
loss depends on the lower groups only; it is independent of the cardinality
and rank of Q. -/
theorem graded_top_count_lower (m : ℕ) (d : I → ℕ)
    (f : (∀ i, G i) × Q → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (𝔼 a : (∀ i, G i) × Q, f a)^(2*m+2)/((∏ i, (Fintype.card (G i))^(d i) : ℕ) : ℝ) ≤
      fiberedEvenCount m (fun a c j ↦ gradedSample d a c j.val) (fun a z ↦ f (a,z)) := by
  have h := fiberedEvenCount_lower_product m (fun a c j ↦ gradedSample d a c j.val)
    (fun a j ↦ gradedSample_zero d a j.val) f hf
  simpa only [gradedCoefficientCard] using h
end Graded

#print axioms fiberedEvenCount_lower
#print axioms graded_top_count_lower
end Erdos3TopDegreeFiberCounting
