import Submission.FiniteSamplingMoments
import Submission.FourierMultilinearTransfer

/-! Counting for a model with a diagonal coefficient slice. This accommodates
mixed-degree factors, at the explicit cost of the reciprocal size of their
nonconstant coefficient space. It does not assert a structural decomposition. -/
namespace Erdos3AnchoredModelCounting
open Finset Erdos3FiniteSamplingMoments Erdos3FourierMultilinearTransfer
open scoped BigOperators Classical
set_option maxHeartbeats 3000000

variable {Y C I : Type*} [Fintype Y] [Nonempty Y] [Fintype C] [Zero C] [Fintype I]

noncomputable def anchoredCount (M : Y → C → I → Y) (f : Y → ℝ) : ℝ :=
  𝔼 y : Y, 𝔼 c : C, ∏ i : I, f (M y c i)

/-- The zero-coefficient slice consists of constant configurations. Its exact
probability is 1/|C|; no density-independent estimate hides that loss. -/
theorem anchoredCount_lower (M : Y → C → I → Y) (hM : ∀ y i, M y 0 i = y)
    (f : Y → ℝ) (hf : ∀ y, 0 ≤ f y) (hI : Even (Fintype.card I)) :
    (𝔼 y : Y, f y)^(Fintype.card I)/(Fintype.card C : ℝ) ≤ anchoredCount M f := by
  have hs (y : Y) : (f y)^(Fintype.card I) ≤ ∑ c : C, ∏ i : I, f (M y c i) := by
    have ht := single_le_sum (f := fun c : C ↦ ∏ i : I, f (M y c i)) (fun c (_ : c ∈ (univ : Finset C)) ↦
      prod_nonneg (fun i _ ↦ hf (M y c i))) (mem_univ (0 : C))
    simpa only [hM,prod_const,card_univ] using ht
  calc
    _ ≤ (𝔼 y : Y, (f y)^(Fintype.card I))/(Fintype.card C : ℝ) :=
      div_le_div_of_nonneg_right (expect_even_pow_le hI f) (Nat.cast_nonneg _)
    _ = 𝔼 y : Y, (f y)^(Fintype.card I)/(Fintype.card C : ℝ) := expect_div _ _ _
    _ ≤ anchoredCount M f := by
      apply expect_le_expect
      intro y _
      rw [Fintype.expect_eq_sum_div_card]
      exact div_le_div_of_nonneg_right (hs y) (Nat.cast_nonneg _)

variable {G X : Type*} [AddCommGroup G] [Fintype G] [Fintype X]

theorem anchored_model_transfer_lower (M : G → C → I → G)
    (hM : ∀ y i, M y 0 i = y) (f : G → ℝ) (hf : ∀ y, 0 ≤ f y)
    (hI : Even (Fintype.card I)) (v : X → I → G) {ε : ℝ}
    (hdisc : ∀ χ : I → AddChar G ℂ,
      ‖(𝔼 x : X, ∏ i, χ i (v x i))-
        (𝔼 p : G × C, ∏ i, χ i (M p.1 p.2 i))‖ ≤ ε) :
    (𝔼 y : G, f y)^(Fintype.card I)/(Fintype.card C : ℝ)-
      ε*fourierMass (fun y ↦ (f y : ℂ))^(Fintype.card I) ≤
      𝔼 x : X, ∏ i, f (v x i) := by
  have ht := multilinear_transfer_real (fun _ : I ↦ f) v (fun p : G × C ↦ M p.1 p.2) hdisc
  simp only [prod_const,card_univ] at ht
  have he : (𝔼 p : G × C, ∏ i, f (M p.1 p.2 i)) = anchoredCount M f :=
    expect_product _ _ _
  rw [he] at ht
  have hl := anchoredCount_lower M hM f hf hI
  have hh := (abs_le.mp ht).1
  linarith

#print axioms anchoredCount_lower
#print axioms anchored_model_transfer_lower
end Erdos3AnchoredModelCounting
