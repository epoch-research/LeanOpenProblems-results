import Submission.QuarticGraphExplore

/-! Positive even-degree polynomial graphs have bounded sum fibers.
This supports interpolation of prescribed finite graph data. -/
namespace Erdos66EvenPolynomialGraph
open Polynomial Erdos66TranslatedGraphPartition Erdos66QuarticGraph
open scoped Classical
set_option maxHeartbeats 2500000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma reflectionPolynomial_degree (t : F) : (C t-X:F[X]).natDegree=1 := by
  rw [show (C t-X:F[X])=-(X-C t) by ring,natDegree_neg,natDegree_X_sub_C]

lemma reflectionPolynomial_leading (t : F) : (C t-X:F[X]).leadingCoeff=-1 := by
  rw [show (C t-X:F[X])=-(X-C t) by ring,leadingCoeff_neg,leadingCoeff_X_sub_C]

/-- Cancellation of the leading term is impossible for even degree in odd
characteristic, independently of every lower coefficient. -/
theorem even_polynomial_bounded (hF : ringChar F≠2) (P : F[X])
    (hpos : 0<P.natDegree) (heven : Even P.natDegree) :
    HasBoundedSums (fun x ↦ P.eval x) P.natDegree := by
  have hP : P≠0 := ne_zero_of_natDegree_gt hpos
  have hlc : P.leadingCoeff≠0 := mt leadingCoeff_eq_zero.mp hP
  intro t s
  let Q : F[X] := P+P.comp (C t-X)-C s
  have hcomp : (P.comp (C t-X)).natDegree=P.natDegree := by
    rw [natDegree_comp,reflectionPolynomial_degree,mul_one]
  have hclead : (P.comp (C t-X)).leadingCoeff=P.leadingCoeff := by
    rw [leadingCoeff_comp (by rw [reflectionPolynomial_degree]; decide),
      reflectionPolynomial_leading,heven.neg_one_pow,mul_one]
  have hccomp : (P.comp (C t-X)).coeff P.natDegree=P.leadingCoeff := by
    rw [←hcomp,coeff_natDegree,hclead]
  have hdeg : Q.natDegree≤P.natDegree := by
    dsimp only [Q]
    rw [natDegree_sub_C]
    exact (natDegree_add_le _ _).trans (by rw [hcomp,max_self])
  have hc : Q.coeff P.natDegree=2*P.leadingCoeff := by
    dsimp only [Q]
    rw [coeff_sub,coeff_add,coeff_natDegree,hccomp,coeff_C]
    have hd0 : P.natDegree≠0 := Nat.ne_of_gt hpos
    simp only [hd0,if_false,sub_zero]
    ring
  have hQ : Q≠0 := by
    intro hzero
    have he : (2:F)*P.leadingCoeff=0 := by rw [←hc,hzero,coeff_zero]
    exact mul_ne_zero (Ring.two_ne_zero hF) hlc he
  have hEval (x : F) : Q.eval x=P.eval x+P.eval (t-x)-s := by
    simp only [Q,eval_sub,eval_add,eval_comp,eval_C,eval_X]
  have he : {x : F // P.eval x+P.eval (t-x)=s} ≃ {x : F // Q.eval x=0} :=
    Equiv.subtypeEquivRight (fun x ↦ by rw [hEval,sub_eq_zero])
  rw [Fintype.card_congr he]
  exact (polynomial_fiber_bound Q hQ).trans hdeg

end Erdos66EvenPolynomialGraph
