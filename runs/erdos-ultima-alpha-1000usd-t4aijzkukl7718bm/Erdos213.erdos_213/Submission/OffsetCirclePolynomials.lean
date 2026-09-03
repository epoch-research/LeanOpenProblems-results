import Submission.OffsetCircleCover

/-! Exact pairwise coprimality of the offset-circle distance kernels.
This is a branch-separation result, not a bound for rational-distance sets. -/
namespace Erdos213.OffsetCircle
open Polynomial
noncomputable section

private def qpoly {F : Type*} [CommRing F] (a b c : F) : F[X] :=
  C a*X^2+C b*X+C c
private def qres {F : Type*} [CommRing F] (a b c d e f : F) : F :=
  (a*f-c*d)^2-(a*e-b*d)*(b*f-c*e)

private lemma qres_coprime {F : Type*} [Field F] (a b c d e f : F)
    (hr : qres a b c d e f ≠ 0) : IsCoprime (qpoly a b c) (qpoly d e f) := by
  let r := qres a b c d e f
  let L : F[X] := C (a*e-b*d)*X-C (a*f-c*d)
  let U : F[X] := C d*L+C e*C (a*e-b*d)
  let V : F[X] := -(C a*L+C b*C (a*e-b*d))
  have he : U*qpoly a b c+V*qpoly d e f=C r := by
    dsimp [U,V,L,r,qpoly,qres]
    simp only [map_mul,map_sub,map_pow]
    ring
  refine ⟨C r⁻¹*U,C r⁻¹*V,?_⟩
  calc
    C r⁻¹*U*qpoly a b c+C r⁻¹*V*qpoly d e f=
        C r⁻¹*(U*qpoly a b c+V*qpoly d e f) := by ring
    _=C r⁻¹*C r := by rw [he]
    _=1 := by rw [← map_mul,inv_mul_cancel₀ hr,map_one]

def kernelPoly (c t : ℚ) : ℚ[X] :=
  qpoly (c^2+(c-1)^2*t^2) (2*t) ((c+1)^2+c^2*t^2)
def infinityPoly (c : ℚ) : ℚ[X] := qpoly ((c-1)^2) 0 (c^2)
def kernelResultant (c t u : ℚ) : ℚ :=
  qres (c^2+(c-1)^2*t^2) (2*t) ((c+1)^2+c^2*t^2)
    (c^2+(c-1)^2*u^2) (2*u) ((c+1)^2+c^2*u^2)

lemma kernelPoly_eval (c t s : ℚ) : (kernelPoly c t).eval s=kernel c 1 t s := by
  dsimp [kernelPoly,qpoly,kernel]
  simp only [eval_add,eval_mul,eval_pow,eval_C,eval_X]
  ring
lemma infinityPoly_eval (c s : ℚ) : (infinityPoly c).eval s=anchorB c s := by
  dsimp [infinityPoly,qpoly,anchorB]
  simp only [eval_add,eval_mul,eval_pow,eval_C,eval_X]
  ring

lemma kernelResultant_formula (c t u : ℚ) : kernelResultant c t u=
    (t-u)^2*((2*c^2-1)^2*(t-u)^2+4*c^2*((c+1)+(c-1)*t*u)^2) := by
  dsimp [kernelResultant,qres]
  ring
lemma kernelResultant_pos (c t u : ℚ) (htu : t ≠ u) : 0<kernelResultant c t u := by
  rw [kernelResultant_formula]
  have h1 : 0<(2*c^2-1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr (twice_square_ne_one c))
  have h2 : 0<(t-u)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr htu)
  positivity

lemma distinct_kernel_polynomials_coprime (c t u : ℚ) (htu : t ≠ u) :
    IsCoprime (kernelPoly c t) (kernelPoly c u) :=
  qres_coprime _ _ _ _ _ _ (ne_of_gt (kernelResultant_pos c t u htu))

lemma infinity_kernel_polynomials_coprime (c t : ℚ) :
    IsCoprime (infinityPoly c) (kernelPoly c t) := by
  apply qres_coprime
  have he : qres ((c-1)^2) 0 (c^2)
      (c^2+(c-1)^2*t^2) (2*t) ((c+1)^2+c^2*t^2)=resBK c t := by
    dsimp [qres,resBK]
    ring
  rw [he]
  exact ne_of_gt (resBK_pos c t)

private lemma qpoly_separable {F : Type*} [Field F] (a b c : F)
    (ha : a ≠ 0) (hd : b^2-4*a*c ≠ 0) : (qpoly a b c).Separable := by
  have he : (qpoly a b c).derivative=qpoly 0 (2*a) b := by
    simp [qpoly,derivative_add,derivative_mul,derivative_pow,map_mul]
    ring
  change IsCoprime _ _
  rw [he]
  apply qres_coprime
  have hr : qres a b c 0 (2*a) b = -a^2*(b^2-4*a*c) := by dsimp [qres]; ring
  rw [hr]
  exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 ha)) hd

lemma kernelPoly_separable (c t : ℚ) (hc : c ≠ 0)
    (hn : (c+1)+(c-1)*t^2 ≠ 0) : (kernelPoly c t).Separable := by
  have hc2 : 0<c^2 := sq_pos_of_ne_zero hc
  apply qpoly_separable
  · exact ne_of_gt (show 0<c^2+(c-1)^2*t^2 by positivity)
  · have he : (2*t)^2-4*(c^2+(c-1)^2*t^2)*((c+1)^2+c^2*t^2)=
        -4*c^2*((c+1)+(c-1)*t^2)^2 := by ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hc)) (pow_ne_zero 2 hn)

lemma infinityPoly_separable (c : ℚ) (hc : c ≠ 0) (hm : c ≠ 1) :
    (infinityPoly c).Separable := by
  apply qpoly_separable
  · exact pow_ne_zero 2 (sub_ne_zero.mpr hm)
  · have he : (0 : ℚ)^2-4*(c-1)^2*c^2 = -4*(c-1)^2*c^2 := by ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 (sub_ne_zero.mpr hm)))
      (pow_ne_zero 2 hc)

#print axioms kernelPoly_separable
#print axioms infinityPoly_separable
#print axioms kernelPoly_eval
#print axioms kernelResultant_formula
#print axioms distinct_kernel_polynomials_coprime
#print axioms infinity_kernel_polynomials_coprime
end
end Erdos213.OffsetCircle
