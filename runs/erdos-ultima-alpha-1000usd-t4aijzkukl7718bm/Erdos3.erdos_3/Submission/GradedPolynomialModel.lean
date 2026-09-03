import Submission.AnchoredModelCounting
import Submission.LocalPolynomialPhaseExtension

/-! A mixed-degree finite polynomial model with its exact coefficient-space
loss. Unlike the pure-top-degree model, lower-degree coordinates are allowed.
No approximation or equidistribution theorem for arbitrary sets is asserted. -/
namespace Erdos3GradedPolynomialModel
open Finset Erdos3AnchoredModelCounting Erdos3LocalPolynomialPhaseExtension Erdos3HigherPhaseDifferences
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {G : I → Type*} [∀ i, AddCommGroup (G i)]

noncomputable def gradedSample (d : I → ℕ) (a : ∀ i, G i)
    (c : ∀ i, Fin (d i) → G i) (j : ℕ) (i : I) : G i :=
  a i+∑ t : Fin (d i), j.choose (t.val+1) • c i t

lemma gradedSample_zero (d : I → ℕ) (a : ∀ i, G i) (j : ℕ) :
    gradedSample d a 0 j = a := by
  funext i
  simp only [gradedSample,Pi.zero_apply,nsmul_zero,sum_const_zero,add_zero]

lemma gradedSample_add (d : I → ℕ) (a b : ∀ i, G i)
    (c e : ∀ i, Fin (d i) → G i) (j : ℕ) :
    gradedSample d (a+b) (c+e) j = gradedSample d a c j+gradedSample d b e j := by
  funext i
  simp only [gradedSample,Pi.add_apply,smul_add,sum_add_distrib]
  abel

lemma gradedSample_difference_zero (d : I → ℕ) (a : ∀ i, G i)
    (c : ∀ i, Fin (d i) → G i) (i : I) :
    diffIter (d i+1) (fun j ↦ gradedSample d a c j i) = 0 := by
  have hconst : diffIter (d i+1) (fun _j : ℕ ↦ a i) = 0 := by
    simpa only [Nat.choose_zero_right,one_smul] using
      diffIter_choose_smul_zero (a i) (j := 0) (k := d i+1) (by omega)
  have ht (t : Fin (d i)) : diffIter (d i+1) (fun j : ℕ ↦ j.choose (t.val+1) • c i t) = 0 :=
    diffIter_choose_smul_zero _ (by omega)
  have he : (fun j ↦ gradedSample d a c j i) =
      (fun _j : ℕ ↦ a i)+∑ t : Fin (d i), (fun j : ℕ ↦ j.choose (t.val+1) • c i t) := by
    funext j
    simp only [gradedSample,Pi.add_apply,sum_apply]
  rw [he,diffIter,fwdDiff_iter_add,fwdDiff_iter_finset_sum]
  change diffIter (d i+1) (fun _j : ℕ ↦ a i)+∑ t : Fin (d i), diffIter (d i+1)
    (fun j : ℕ ↦ j.choose (t.val+1) • c i t) = 0
  simp only [hconst,ht,sum_const_zero,add_zero]

variable [∀ i, Fintype (G i)]

noncomputable def gradedModelCount (d : I → ℕ) (k : ℕ) (f : (∀ i, G i) → ℝ) : ℝ :=
  𝔼 a : (∀ i, G i), 𝔼 c : (∀ i, Fin (d i) → G i), ∏ j : Fin k, f (gradedSample d a c j.val)

lemma gradedCoefficientCard (d : I → ℕ) :
    Fintype.card (∀ i, Fin (d i) → G i) = ∏ i, (Fintype.card (G i))^(d i) := by
  rw [Fintype.card_pi]
  apply prod_congr rfl
  intro i _
  simp only [Fintype.card_fun,Fintype.card_fin]

/-- The denominator records every nonconstant coefficient, including those of
lower degree. It is exponential in the total weighted rank for fixed field. -/
theorem gradedModelCount_lower (d : I → ℕ) (k : ℕ) (hk : Even k)
    (f : (∀ i, G i) → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (𝔼 a : (∀ i, G i), f a)^k/((∏ i, (Fintype.card (G i))^(d i) : ℕ) : ℝ) ≤
      gradedModelCount d k f := by
  have h := anchoredCount_lower (I := Fin k) (fun a c j ↦ gradedSample d a c j.val)
    (fun a j ↦ gradedSample_zero d a j.val) f hf (by simpa only [Fintype.card_fin] using hk)
  simpa only [Fintype.card_fin,gradedCoefficientCard] using h

/-- When each coefficient group has cardinality p, the exact loss is p raised
to the sum of the assigned degrees, rather than a hidden constant. -/
theorem gradedModelCount_lower_equal_card (d : I → ℕ) (k p : ℕ) (hk : Even k)
    (hp : ∀ i, Fintype.card (G i) = p)
    (f : (∀ i, G i) → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (𝔼 a : (∀ i, G i), f a)^k/(p : ℝ)^(∑ i, d i) ≤ gradedModelCount d k f := by
  have h := gradedModelCount_lower d k hk f hf
  simpa only [hp,prod_pow_eq_pow_sum,Nat.cast_pow] using h

#print axioms gradedSample_difference_zero
#print axioms gradedModelCount_lower
#print axioms gradedModelCount_lower_equal_card
end Erdos3GradedPolynomialModel
