import Submission.InterceptEdgePolynomialExplore
import Submission.InterceptCurveExplore

/-! A nonzero polynomial of degree at most eight detects three distinct
collision edges lying on one reflected translated intercept curve. -/
namespace Erdos66InterceptConcurrencyPolynomial
open Polynomial Erdos66InterceptEdgePolynomial Erdos66InterceptCurve
open scoped Polynomial Classical
set_option maxHeartbeats 2200000
variable {F : Type*} [Field F]

noncomputable def pairLinear (w : F) (e f : F × F) : F[X] :=
  C (2*(edgeSum e-edgeSum f))*X+C (w*(edgeSum e-edgeSum f)+(edgeProd e-edgeProd f))

lemma pairLinear_eval (w a : F) (e f : F × F) :
    (pairLinear w e f).eval a=(2*a+w)*(edgeSum e-edgeSum f)+(edgeProd e-edgeProd f) := by
  simp only [pairLinear,eval_add,eval_mul,eval_C,eval_X]
  ring

lemma pairLinear_ne_zero (h2 : (2 : F)≠0) (w : F) (e f : F × F) (h : ¬SameEdge e f) :
    pairLinear w e f≠0 := by
  intro hz
  have h1 := congrArg (fun P : F[X] ↦ P.coeff 1) hz
  simp only [pairLinear,coeff_add,coeff_C_mul,coeff_X_one,coeff_C,one_ne_zero,if_false,
    mul_one,add_zero,coeff_zero] at h1
  have hs : edgeSum e=edgeSum f := sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left h2)
  have h0 := congrArg (fun P : F[X] ↦ P.coeff 0) hz
  simp only [pairLinear,coeff_add,coeff_C_mul,coeff_X_zero,coeff_C,if_true,
    mul_zero,zero_add,coeff_zero,hs,sub_self,mul_zero,zero_add] at h0
  exact h (sameEdge_of_sum_prod e f hs (sub_eq_zero.mp h0))

noncomputable def concurrencyPolynomial (w : F) (e f g : F × F) : F[X] :=
  tripleNorm e f g (pairLinear w f g) (pairLinear w g e) (pairLinear w e f)

lemma concurrencyPolynomial_ne_zero (h2 : (2 : F)≠0) (w : F) (e f g : F × F)
    (he : e.1≠e.2) (hef : ¬SameEdge e f) (hfg : ¬SameEdge f g) (hge : ¬SameEdge g e) :
    concurrencyPolynomial w e f g≠0 := by
  exact tripleNorm_ne_zero h2 e f g he hef _ _ _
    (pairLinear_ne_zero h2 w f g hfg) (pairLinear_ne_zero h2 w g e hge)

def EdgeHit (a w q t : F) (e : F × F) (k : F) : Prop :=
  k^2=(a+e.1)*(a+e.2) ∧ value (a+w) (q-k)=t-((a+e.1)+(a+e.2))

lemma hit_identity (a w q t : F) (e : F × F) (k : F) (hw : a+w≠0)
    (h : EdgeHit a w q t e k) :
    (a+w)*((a+e.1)+(a+e.2))+(a+e.1)*(a+e.2)=
      (a+w)*t-(a+w)^2-q^2+2*q*k := by
  obtain ⟨hk,hv⟩ := h
  have hv' : (q-k)^2/(a+w)=t-((a+e.1)+(a+e.2))-(a+w) := by
    dsimp [value] at hv
    linear_combination hv
  have hh := (div_eq_iff hw).mp hv'
  linear_combination hh-hk

lemma hits_difference (a w q t : F) (e f : F × F) (k l : F) (hw : a+w≠0)
    (he : EdgeHit a w q t e k) (hf : EdgeHit a w q t f l) :
    (pairLinear w e f).eval a=2*q*(k-l) := by
  rw [pairLinear_eval]
  have h1 := hit_identity a w q t e k hw he
  have h2 := hit_identity a w q t f l hw hf
  dsimp [edgeSum,edgeProd]
  linear_combination h1-h2

lemma three_hits_root (a w q t : F) (e f g : F × F) (k l m : F) (hw : a+w≠0)
    (he : EdgeHit a w q t e k) (hf : EdgeHit a w q t f l) (hg : EdgeHit a w q t g m) :
    (concurrencyPolynomial w e f g).eval a=0 := by
  apply tripleNorm_eval_zero e f g _ _ _ a k l m
  · simpa only [edgePolynomial_eval] using he.1
  · simpa only [edgePolynomial_eval] using hf.1
  · simpa only [edgePolynomial_eval] using hg.1
  · rw [hits_difference a w q t f g l m hw hf hg,
      hits_difference a w q t g e m k hw hg he,
      hits_difference a w q t e f k l hw he hf]
    ring

lemma natDegree_mul_bound (P Q : F[X]) (m n : ℕ) (hP : P.natDegree≤ m) (hQ : Q.natDegree≤ n) :
    (P*Q).natDegree≤ m+n := natDegree_mul_le.trans (Nat.add_le_add hP hQ)

lemma natDegree_add_bound (P Q : F[X]) (n : ℕ) (hP : P.natDegree≤ n) (hQ : Q.natDegree≤ n) :
    (P+Q).natDegree≤ n := (natDegree_add_le P Q).trans (max_le hP hQ)

lemma natDegree_sub_bound (P Q : F[X]) (n : ℕ) (hP : P.natDegree≤ n) (hQ : Q.natDegree≤ n) :
    (P-Q).natDegree≤ n := (natDegree_sub_le P Q).trans (max_le hP hQ)

lemma natDegree_pow_bound (P : F[X]) (m n : ℕ) (hP : P.natDegree≤ m) :
    (P^n).natDegree≤ n*m := natDegree_pow_le.trans (Nat.mul_le_mul_left n hP)

lemma edgePolynomial_degree (e : F × F) : (edgePolynomial e).natDegree≤ 2 := by
  apply natDegree_mul_bound _ _ 1 1
  · simp [linearFactor]
  · simp [linearFactor]

lemma pairLinear_degree (w : F) (e f : F × F) : (pairLinear w e f).natDegree≤ 1 := by
  apply natDegree_add_bound _ _ 1
  · have hh := natDegree_mul_bound (C (2*(edgeSum e-edgeSum f))) X 0 1 (by rw [natDegree_C]) (by simp)
    exact hh
  · rw [natDegree_C]
    omega

lemma tripleNorm_degree (e f g : F × F) (A B C' : F[X])
    (hA : A.natDegree≤ 1) (hB : B.natDegree≤ 1) (hC : C'.natDegree≤ 1) :
    (tripleNorm e f g A B C').natDegree≤ 8 := by
  have term (e : F × F) (A : F[X]) (hA : A.natDegree≤ 1) :
      (A^2*edgePolynomial e).natDegree≤ 4 :=
    natDegree_mul_bound _ _ 2 2 (natDegree_pow_bound A 1 2 hA) (edgePolynomial_degree e)
  have hsum := natDegree_add_bound _ _ 4 (term e A hA) (term f B hB)
  have hsub := natDegree_sub_bound _ _ 4 hsum (term g C' hC)
  have hleft := natDegree_pow_bound _ 4 2 hsub
  have hAB := natDegree_mul_bound (C (2 : F)*A) B 1 1
    (natDegree_mul_bound _ _ 0 1 (by simp) hA) hB
  have hright := natDegree_mul_bound _ _ 4 4 (natDegree_pow_bound _ 2 2 hAB)
    (natDegree_mul_bound _ _ 2 2 (edgePolynomial_degree e) (edgePolynomial_degree f))
  exact natDegree_sub_bound _ _ 8 hleft hright

lemma concurrencyPolynomial_degree (w : F) (e f g : F × F) :
    (concurrencyPolynomial w e f g).natDegree≤ 8 :=
  tripleNorm_degree e f g _ _ _ (pairLinear_degree w f g) (pairLinear_degree w g e)
    (pairLinear_degree w e f)

end Erdos66InterceptConcurrencyPolynomial
