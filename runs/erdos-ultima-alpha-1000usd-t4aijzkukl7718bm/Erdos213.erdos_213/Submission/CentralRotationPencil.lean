import FormalConjecturesUtil

/-! Necessary sextic square conditions for a free rational rotation in the
central mixed-circumcenter construction. No existence theorem is asserted. -/
namespace Erdos213.CentralRotationPencil
set_option maxHeartbeats 2000000

def gPoly {K : Type*} [CommRing K] (L C : K) : K :=
  L^6-6*C*L^5+9*L^4+8*C*L^3-24*L^2+16

def mPoly {K : Type*} [CommRing K] (L C : K) : K :=
  L^6-6*C*L^5+(8+C^2)*L^4+8*C*L^3-24*L^2+16

lemma rotation_relation {K : Type*} [CommRing K]
    (L R x u v p q : K)
    (hp : p^2+q^2=1) (hn : u^2+v^2=R+1)
    (hd : u^2-v^2=L*(1-R)) (hx : u*v=x)
    (hm : L^2*(p*u-q*v)^2=L^2+(2-L^2)*(R-1)) :
    2*(2*p*q)*L^2*x=((p^2-q^2)*L^3-3*L^2+4)*(1-R) := by
  linear_combination
    L^2*(u^2+v^2)*hp + L^2*hn + L^2*(p^2-q^2)*hd -
    4*p*q*L^2*hx - 2*hm

lemma rotation_unit {K : Type*} [CommRing K] (p q : K) (h : p^2+q^2=1) :
    (p^2-q^2)^2+(2*p*q)^2=1 := by
  linear_combination (p^2+q^2+1)*h

lemma m_norm_identity {K : Type*} [CommRing K] (L C S A : K)
    (hc : C^2+S^2=1) (ha : A^2=L^2-1) :
    mPoly L C=(C*L^3-3*L^2+4)^2+S^2*L^4*A^2 := by
  unfold mPoly
  linear_combination -L^4*(L^2-1)*hc - S^2*L^4*ha

lemma g_sub_m {K : Type*} [CommRing K] (L C S : K)
    (hc : C^2+S^2=1) : gPoly L C=mPoly L C+S^2*L^4 := by
  unfold gPoly mPoly
  linear_combination -L^4*hc

lemma cleared_m_square {K : Type*} [CommRing K] (L C S A x y r : K)
    (hc : C^2+S^2=1) (ha : A^2=L^2-1) (hr : r^2=x^2+y^2)
    (hy : 2*y=(1-r^2)*A)
    (hx : 2*S*L^2*x=(C*L^3-3*L^2+4)*(1-r^2)) :
    mPoly L C*(1-r^2)^2=(2*S*L^2*r)^2 := by
  rw [m_norm_identity L C S A hc ha]
  linear_combination
    -(2*S*L^2*x+(C*L^3-3*L^2+4)*(1-r^2))*hx -
    S^2*L^4*(2*y+(1-r^2)*A)*hy - 4*S^2*L^4*hr

lemma cleared_g_square {K : Type*} [CommRing K] (L C S A x y r : K)
    (hc : C^2+S^2=1) (ha : A^2=L^2-1) (hr : r^2=x^2+y^2)
    (hy : 2*y=(1-r^2)*A)
    (hx : 2*S*L^2*x=(C*L^3-3*L^2+4)*(1-r^2)) :
    gPoly L C*(1-r^2)^2=(S*L^2*(1+r^2))^2 := by
  rw [g_sub_m L C S hc]
  linear_combination cleared_m_square L C S A x y r hc ha hr hy hx

/-- Two necessary rational squares. The rational rotation parameter is free;
these conditions are not asserted to be sufficient for the missing edges. -/
theorem necessary_square_values (L C S A x y r : ℚ)
    (hc : C^2+S^2=1) (ha : A^2=L^2-1) (hr : r^2=x^2+y^2)
    (hy : 2*y=(1-r^2)*A)
    (hx : 2*S*L^2*x=(C*L^3-3*L^2+4)*(1-r^2))
    (hR : r^2≠1) : IsSquare (mPoly L C) ∧ IsSquare (gPoly L C) := by
  have hn : 1-r^2≠0 := sub_ne_zero.mpr (Ne.symm hR)
  have hm := cleared_m_square L C S A x y r hc ha hr hy hx
  have hg := cleared_g_square L C S A x y r hc ha hr hy hx
  constructor
  · refine ⟨(2*S*L^2*r)/(1-r^2),?_⟩
    field_simp
    nlinarith only [hm]
  · refine ⟨(S*L^2*(1+r^2))/(1-r^2),?_⟩
    field_simp
    nlinarith only [hg]

/-- The elementary triple-angle factorization behind the necessary cover. -/
lemma triple_angle_identity {K : Type*} [CommRing K] (L : K) :
    L^6-(3*L^2-4)^2=(L^2-1)*(L^2-4)^2 := by ring

/-- The most direct choice C=(3L^2-4)/L^3 makes x vanish. Such a branch
cannot repair the general-position defect of the mixed central model. -/
lemma aligned_abscissa_zero {L C S x r : ℚ} (hL : L≠0) (hS : S≠0)
    (hc : C*L^3=3*L^2-4)
    (hx : 2*S*L^2*x=(C*L^3-3*L^2+4)*(1-r^2)) : x=0 := by
  have hh : 2*S*L^2*x=0 := by rw [hc] at hx; nlinarith only [hx]
  exact (mul_eq_zero.mp hh).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) hS) (pow_ne_zero _ hL))

#print axioms rotation_relation
#print axioms necessary_square_values
#print axioms triple_angle_identity
#print axioms aligned_abscissa_zero
end Erdos213.CentralRotationPencil
