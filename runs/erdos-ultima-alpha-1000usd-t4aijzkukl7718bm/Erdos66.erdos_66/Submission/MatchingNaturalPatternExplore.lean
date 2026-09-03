import Submission.NaturalPositivePatternExplore
import Submission.BernoulliMatchingPolynomialExplore

/-! Matching polynomials as positive finite-coordinate natural patterns. -/
namespace Erdos66MatchingNaturalPattern
open Erdos66NaturalPositivePattern Erdos66BernoulliMatchingPolynomial Erdos66MatchingPartition
  Erdos66FiniteBernoulli
open scoped Classical
set_option maxHeartbeats 1600000

noncomputable def matchingPattern {κ : Type} (L : ℕ) (S : Finset κ)
    (E : κ → Finset (Fin (L+1))) (t : ℝ) (ht : 0 ≤ t) : Pattern where
  Term := Finset κ
  terms := matchings S E
  coeff := fun M ↦ (Real.exp t-1)^M.card
  support := fun M ↦ (M.biUnion E).image Fin.val
  nonneg := fun M _ ↦ pow_nonneg (sub_nonneg.mpr (Real.one_le_exp ht)) _

lemma matchingPattern_eval {κ : Type} (L : ℕ) (S : Finset κ) (E : κ → Finset (Fin (L+1)))
    (t : ℝ) (ht : 0 ≤ t) (x : ℕ → ℝ) :
    (matchingPattern L S E t ht).eval x=matchingPoly S E t (fun i ↦ x i.val) := by
  simp only [Pattern.eval,matchingPattern,matchingPoly]
  apply Finset.sum_congr (by ext M; simp [matchings])
  intro M hM
  congr 1
  convert Finset.prod_image (s := M.biUnion E) (f := x) (g := fun i : Fin (L+1) ↦ i.val)
    Fin.val_injective.injOn using 1
  apply Finset.prod_congr
  · ext i; simp
  · intro i hi; rfl

noncomputable def zeroPattern : Pattern where
  Term := Unit
  terms := ∅
  coeff := fun _ ↦ 0
  support := fun _ ↦ ∅
  nonneg := fun _ _ ↦ le_rfl

@[simp] lemma zeroPattern_eval (x : ℕ → ℝ) : zeroPattern.eval x=0 := by simp [zeroPattern,Pattern.eval]
@[simp] lemma zeroPattern_value (f : ℕ → Bool) : zeroPattern.value f=0 := zeroPattern_eval _

noncomputable def scalePattern (w : ℝ) (hw : 0 ≤ w) (P : Pattern) : Pattern where
  Term := P.Term
  terms := P.terms
  coeff := fun k ↦ w*P.coeff k
  support := P.support
  nonneg := fun k hk ↦ mul_nonneg hw (P.nonneg k hk)

@[simp] lemma scalePattern_eval (w : ℝ) (hw : 0 ≤ w) (P : Pattern) (x : ℕ → ℝ) :
    (scalePattern w hw P).eval x=w*P.eval x := by
  simp only [scalePattern,Pattern.eval,Finset.mul_sum,mul_assoc]

@[simp] lemma scalePattern_value (w : ℝ) (hw : 0 ≤ w) (P : Pattern) (f : ℕ → Bool) :
    (scalePattern w hw P).value f=w*P.value f := scalePattern_eval _ _ _ _

end Erdos66MatchingNaturalPattern
