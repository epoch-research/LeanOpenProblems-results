import FormalConjecturesUtil

/-! An explicit rational-median family and its additional square condition.
This file does not assert existence of a general-position eight-point set. -/

namespace Erdos213.MedianFamily

def a (r : ℚ) : ℚ := r^5+r^4-6*r^3+26*r^2+9*r+9
def b (r : ℚ) : ℚ := 2*(3*r^4+10*r^2-9)
def c (r : ℚ) : ℚ := r^5-r^4-6*r^3-26*r^2+9*r-9
def u (r : ℚ) : ℚ := r^5+3*r^4+26*r^3-18*r^2+9*r+27
def v (r : ℚ) : ℚ := -2*r*(r^4-10*r^2-27)
def w (r : ℚ) : ℚ := r^5-3*r^4+26*r^3+18*r^2+9*r-27

def discriminant (a b c : ℚ) : ℚ :=
  a^4+b^4+c^4-a^2*b^2-a^2*c^2-b^2*c^2

def heron (a b c : ℚ) : ℚ :=
  2*a^2*b^2+2*a^2*c^2+2*b^2*c^2-a^4-b^4-c^4

def extraPolynomial (r : ℚ) : ℚ :=
  r^16-76*r^14+1956*r^12+27308*r^10+67030*r^8+
    245772*r^6+158436*r^4-55404*r^2+6561

def quotientPolynomial (s : ℚ) : ℚ :=
  s^4-76*s^3+1920*s^2+29360*s+31984

lemma median_identities (r : ℚ) :
    u r ^ 2 = 2*a r ^ 2+2*b r ^ 2-c r ^ 2 ∧
    v r ^ 2 = 2*a r ^ 2-b r ^ 2+2*c r ^ 2 ∧
    w r ^ 2 = -a r ^ 2+2*b r ^ 2+2*c r ^ 2 := by
  dsimp [a,b,c,u,v,w]
  constructor
  · ring
  constructor <;> ring

lemma discriminant_factorization (r : ℚ) :
    discriminant (a r) (b r) (c r) = (r^2-3)^2*extraPolynomial r := by
  dsimp [discriminant,a,b,c,extraPolynomial]
  ring

lemma heron_factorization (r : ℚ) :
    heron (a r) (b r) (c r) =
      128*r^2*(r^2-9)*(r^2-1)*(r^2+1)*(r^2+9)*
        (r^4-22*r^2+9)*(r^4+2*r^2+9) := by
  dsimp [heron,a,b,c]
  ring

lemma heron_positive {r : ℚ} (h1 : 1 < r) (h3 : r < 3) :
    0 < heron (a r) (b r) (c r) := by
  have hr : 0 < r := by linarith
  have hlo : 1 < r^2 := by nlinarith
  have hhi : r^2 < 9 := by nlinarith
  have hs : 0 < r^2 := by positivity
  have h4 : r^4 < 9*r^2 := by
    nlinarith [mul_pos hs (show 0 < 9-r^2 by linarith)]
  have hmid : 0 < 22*r^2-r^4-9 := by nlinarith
  have he : heron (a r) (b r) (c r) =
      128*r^2*(9-r^2)*(r^2-1)*(r^2+1)*(r^2+9)*
        (22*r^2-r^4-9)*(r^4+2*r^2+9) := by
    rw [heron_factorization]
    ring
  rw [he]
  have hlow : 0 < r^2-1 := by linarith
  have hupp : 0 < 9-r^2 := by linarith
  positivity

lemma b_positive {r : ℚ} (hr : 1 < r) : 0 < b r := by
  have hs : 1 < r^2 := by nlinarith
  unfold b
  nlinarith [sq_nonneg (r^2)]

lemma sq_ne_three (r : ℚ) : r^2 ≠ 3 := by
  intro h
  have hh : IsSquare (3 : ℚ) := ⟨r, by nlinarith [h]⟩
  norm_num at hh

private lemma isSquare_sq_mul_iff (x y : ℚ) (hx : x ≠ 0) :
    IsSquare (x^2*y) ↔ IsSquare y := by
  constructor
  · rintro ⟨q,hq⟩
    refine ⟨q/x, ?_⟩
    field_simp [hx]
    nlinarith [hq]
  · rintro ⟨q,hq⟩
    refine ⟨x*q, ?_⟩
    rw [hq]
    ring

lemma extra_square_iff (r : ℚ) :
    IsSquare (discriminant (a r) (b r) (c r)) ↔ IsSquare (extraPolynomial r) := by
  rw [discriminant_factorization]
  exact isSquare_sq_mul_iff _ _ (sub_ne_zero.mpr (sq_ne_three r))

lemma quotient_identity {r : ℚ} (hr : r ≠ 0) :
    extraPolynomial r = r^8*quotientPolynomial (r^2+9/r^2) := by
  dsimp [extraPolynomial,quotientPolynomial]
  field_simp [hr]
  ring

lemma quotient_square_iff {r : ℚ} (hr : r ≠ 0) :
    IsSquare (extraPolynomial r) ↔
      IsSquare (quotientPolynomial (r^2+9/r^2)) := by
  rw [quotient_identity hr, show r^8 = (r^4)^2 by ring]
  exact isSquare_sq_mul_iff _ _ (pow_ne_zero 4 hr)

/-- These are the rational parameters found by the bounded exploratory search;
all are degenerate. This is NOT a classification of all rational parameters. -/
lemma listed_parameters_degenerate {r : ℚ}
    (hr : r ∈ ({0,1,-1,3,-3} : Set ℚ)) : heron (a r) (b r) (c r) = 0 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    norm_num [heron_factorization]

/-- Exact lifting condition for the reciprocal quotient parameter. -/
lemma reciprocal_parameter_iff (s : ℚ) :
    (∃ r : ℚ, r ≠ 0 ∧ s = r^2+9/r^2) ↔
      IsSquare (s-6) ∧ IsSquare (s+6) := by
  constructor
  · rintro ⟨r,hr,rfl⟩
    constructor
    · refine ⟨r-3/r, ?_⟩
      field_simp
      ring
    · refine ⟨r+3/r, ?_⟩
      field_simp
      ring
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    let r := (b+a)/2
    let t := (b-a)/2
    have hp : r*t=3 := by
      dsimp [r,t]
      linear_combination (ha-hb)/4
    have hr : r ≠ 0 := by intro h; rw [h,zero_mul] at hp; norm_num at hp
    have hsum : r^2+t^2=s := by
      dsimp [r,t]
      linear_combination -(ha+hb)/2
    refine ⟨r,hr,?_⟩
    have ht : t=3/r := (eq_div_iff hr).mpr (by simpa [mul_comm] using hp)
    have htpow : t^2 = 9/r^2 := by rw [ht,div_pow]; norm_num
    rw [htpow] at hsum
    exact hsum.symm

def ellipticPolynomial (X : ℚ) : ℚ :=
  X^3+492*X^2-3507408*X+2251312704

def ellipticX (s y : ℚ) : ℚ := -2*(y-s^2+38*s-238)

def ellipticY (s y : ℚ) : ℚ := -2*ellipticX s y*s+38*ellipticX s y-47448

lemma quartic_elliptic_identity (s y : ℚ) :
    ellipticY s y ^ 2 - ellipticPolynomial (ellipticX s y) =
      -4*ellipticX s y*(y^2-quotientPolynomial s) := by
  dsimp [ellipticX,ellipticY,ellipticPolynomial,quotientPolynomial]
  ring

lemma quartic_to_elliptic {s y : ℚ} (hy : y^2=quotientPolynomial s) :
    ellipticY s y ^ 2 = ellipticPolynomial (ellipticX s y) := by
  have hh := quartic_elliptic_identity s y
  rw [hy,sub_self,mul_zero] at hh
  exact sub_eq_zero.mp hh

lemma elliptic_to_quartic {X Y : ℚ} (hX : X ≠ 0)
    (hE : Y^2=ellipticPolynomial X) :
    let s := (Y+47448-38*X)/(-2*X)
    (s^2-38*s+238-X/2)^2 = quotientPolynomial s := by
  let s := (Y+47448-38*X)/(-2*X)
  let y := s^2-38*s+238-X/2
  have hx : ellipticX s y = X := by dsimp [ellipticX,y]; ring
  have hy : ellipticY s y = Y := by
    dsimp only [ellipticY]
    rw [hx]
    dsimp [s]
    field_simp
    ring
  have hh := quartic_elliptic_identity s y
  rw [hx,hy,hE,sub_self] at hh
  have hmul : -4*X ≠ 0 := mul_ne_zero (by norm_num) hX
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh.symm).resolve_left hmul)

/-- A point on the explicit elliptic curve plus two square conditions really
lifts to the median family's extra-square cover. No such nondegenerate lift
is asserted to exist. -/
lemma extra_parameter_of_elliptic_point {X Y : ℚ} (hX : X ≠ 0)
    (hE : Y^2=ellipticPolynomial X)
    (hm : IsSquare ((Y+47448-38*X)/(-2*X)-6))
    (hp : IsSquare ((Y+47448-38*X)/(-2*X)+6)) :
    ∃ r : ℚ, r ≠ 0 ∧ IsSquare (extraPolynomial r) := by
  obtain ⟨r,hr,hs⟩ := (reciprocal_parameter_iff _).mpr ⟨hm,hp⟩
  refine ⟨r,hr,(quotient_square_iff hr).mpr ?_⟩
  rw [← hs]
  refine ⟨((Y+47448-38*X)/(-2*X))^2-38*((Y+47448-38*X)/(-2*X))+238-X/2, ?_⟩
  simpa only [pow_two] using (elliptic_to_quartic hX hE).symm

#print axioms reciprocal_parameter_iff
#print axioms quartic_elliptic_identity
#print axioms elliptic_to_quartic
#print axioms extra_parameter_of_elliptic_point

#print axioms median_identities
#print axioms extra_square_iff
#print axioms heron_positive
#print axioms quotient_square_iff

end Erdos213.MedianFamily
