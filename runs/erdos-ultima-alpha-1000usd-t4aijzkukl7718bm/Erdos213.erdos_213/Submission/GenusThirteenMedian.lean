import Mathlib.Tactic

/-! Exact algebra for one exceptional conditional median fiber.
No rank, rational-point classification, or cardinality claim is made here. -/
namespace Erdos213.GenusThirteenMedian

variable {R : Type*} [CommRing R]

def a (t : R) : R := -6*t^2-5*t+2
def b (t : R) : R := 9*t^2+4*t-4
def c (t : R) : R := 9*t^2-t-2
def f (t : R) : R := 2*(a t)^2+2*(b t)^2-(c t)^2
def g (t : R) : R := -(a t)^2+2*(b t)^2+2*(c t)^2
def q (t : R) : R := 153*t^2+12*t-12

def p (u : R) : R := 44064*u^4+88560*u^3+52497*u^2+13176*u+1296
def pHom (u v : R) : R :=
  44064*u^4+88560*u^3*v+52497*u^2*v^2+13176*u*v^3+1296*v^4

def heron (t : R) : R :=
  2*(a t)^2*(b t)^2+2*(a t)^2*(c t)^2+2*(b t)^2*(c t)^2-
  (a t)^4-(b t)^4-(c t)^4

lemma middle_median (t : R) :
    2*(a t)^2-(b t)^2+2*(c t)^2=t^2*q t := by
  dsimp [a,b,c,q]
  ring

lemma discriminant (t : R) :
    (a t)^4+(b t)^4+(c t)^4-(a t)^2*(b t)^2-
      (a t)^2*(c t)^2-(b t)^2*(c t)^2 =
      (3*(5*t-2)*(3*t+2)*(t^2-t+1))^2 := by
  dsimp [a,b,c]
  ring

lemma heron_factor (t : R) :
    heron t=192*(3*t-2)*(3*t-1)*(2*t+1)*(t+2)*t^2*(3*t^2+t-1) := by
  dsimp [heron,a,b,c]
  ring

lemma product_identity (t : R) : pHom (t^2) (t-1)=f t*g t := by
  dsimp [pHom,f,g,a,b,c]
  ring

lemma hom_div (u v : ℚ) (hv : v ≠ 0) : p (u/v)=pHom u v/v^4 := by
  dsimp [p,pHom]
  field_simp

lemma product_quotient (t : ℚ) (ht : t ≠ 1) :
    p (t^2/(t-1))=f t*g t/(t-1)^4 := by
  rw [hom_div _ _ (sub_ne_zero.mpr ht),product_identity]

lemma conic_identities (t : ℚ) (ht : t ≠ 1) :
    (t^2/(t-1))*(t^2/(t-1)-4)=(t*(t-2)/(t-1))^2 ∧
    (t^2/(t-1))*(153*(t^2/(t-1))+12)=t^2*q t/(t-1)^2 := by
  have hd : t-1 ≠ 0 := sub_ne_zero.mpr ht
  dsimp [q]
  constructor <;> field_simp <;> ring

lemma triangle_involution (t : ℚ) (ht : t ≠ 1) :
    a (t/(t-1))= -c t/(t-1)^2 ∧
    b (t/(t-1))= b t/(t-1)^2 ∧
    c (t/(t-1))= -a t/(t-1)^2 ∧
    q (t/(t-1))= q t/(t-1)^2 := by
  have hd : t-1 ≠ 0 := sub_ne_zero.mpr ht
  dsimp [a,b,c,q]
  refine ⟨?_,?_,?_,?_⟩ <;> field_simp <;> ring

/-- Necessary conditions on the rank-two elliptic quotient. -/
lemma necessary_square_conditions (t : ℚ) (ht : t ≠ 1)
    (hf : IsSquare (f t)) (hg : IsSquare (g t)) (hq : IsSquare (q t)) :
    IsSquare (p (t^2/(t-1))) ∧
    IsSquare ((t^2/(t-1))*(t^2/(t-1)-4)) ∧
    IsSquare ((t^2/(t-1))*(153*(t^2/(t-1))+12)) := by
  rw [product_quotient t ht]
  obtain ⟨h₁,h₂⟩ := conic_identities t ht
  rw [h₁,h₂]
  refine ⟨?_,IsSquare.sq _,?_⟩
  · exact (hf.mul hg).div ⟨(t-1)^2, by ring⟩
  · exact ((IsSquare.sq t).mul hq).div (IsSquare.sq _)

/-- The two elementary square conditions recover the original parameter.
The quartic condition recovers only the PRODUCT of the outer median squares. -/
lemma product_cover_lift (u : ℚ) (hu : u ≠ 0) (hp : IsSquare (p u))
    (hd : IsSquare (u*(u-4))) (hq : IsSquare (u*(153*u+12))) :
    ∃ t : ℚ, t ≠ 0 ∧ t ≠ 1 ∧ u=t^2/(t-1) ∧
      IsSquare (q t) ∧ IsSquare (f t*g t) := by
  obtain ⟨r,hr⟩ := hd
  let t := (u+r)/2
  have ht : t^2=u*(t-1) := by dsimp [t]; nlinarith [hr]
  have ht0 : t ≠ 0 := by intro hh; rw [hh] at ht; apply hu; nlinarith [ht]
  have ht1 : t ≠ 1 := by intro hh; rw [hh] at ht; norm_num at ht
  have htden : t-1 ≠ 0 := sub_ne_zero.mpr ht1
  have he : u=t^2/(t-1) := (eq_div_iff htden).mpr (by nlinarith [ht])
  refine ⟨t,ht0,ht1,he,?_,?_⟩
  · obtain ⟨v,hv⟩ := hq
    have hi := (conic_identities t ht1).2
    rw [← he,hv] at hi
    refine ⟨v*(t-1)/t,?_⟩
    field_simp at hi ⊢
    nlinarith [hi]
  · obtain ⟨v,hv⟩ := hp
    rw [he,product_quotient t ht1] at hv
    refine ⟨v*(t-1)^2,?_⟩
    field_simp at hv
    nlinarith [hv]

/-- A positive-area control with two rational doubled medians, not three. -/
lemma partial_control :
    0 < heron (7 : ℚ) ∧ f (7 : ℚ)=678^2 ∧ q (7 : ℚ)=87^2 ∧
    g (7 : ℚ)=698769 ∧ ¬IsSquare (g (7 : ℚ)) := by
  have hn : ¬IsSquare (698769 : ℚ) := by decide +kernel
  norm_num [heron,a,b,c,f,g,q] at hn ⊢

/-- Coefficients of the covariant map from the quartic to its Jacobian. -/
def covH (u : R) : R :=
  418566528*u^4+388536912*u^3+106783947*u^2+1019304*u-1955664

def covJ (u : R) : R :=
  -9973880614656*u^6-17268159179808*u^5-13675294903680*u^4-
  6286365987840*u^3-1691843604480*u^2-241058488320*u-13544423424

lemma covariant_identity (u : R) :
    (covJ u)^2=(covH u)^3+19793781*covH u*(p u)^2+117581343174*(p u)^3 := by
  dsimp [covH,covJ,p]
  ring

lemma elliptic_image (u y : ℚ) (hy : y^2=p u) (hy0 : y ≠ 0) :
    (covJ u/y^3)^2=(covH u/p u)^3+19793781*(covH u/p u)+117581343174 := by
  have hp : p u ≠ 0 := by rw [← hy]; exact pow_ne_zero _ hy0
  have h := covariant_identity u
  rw [← hy] at h ⊢
  field_simp
  nlinarith [h]

#print axioms middle_median
#print axioms discriminant
#print axioms heron_factor
#print axioms product_identity
#print axioms product_quotient
#print axioms conic_identities
#print axioms triangle_involution
#print axioms necessary_square_conditions
#print axioms product_cover_lift
#print axioms partial_control
#print axioms covariant_identity
#print axioms elliptic_image

end Erdos213.GenusThirteenMedian
