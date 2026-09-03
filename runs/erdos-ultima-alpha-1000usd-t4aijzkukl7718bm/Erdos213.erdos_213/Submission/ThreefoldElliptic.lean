import FormalConjecturesUtil

/-! Algebraic elliptic quotients for the threefold-orbit pencils.
The square-lifting hypotheses are not asserted to hold at any new point. -/

set_option maxHeartbeats 2000000
namespace Erdos213.ThreefoldElliptic

def delta (a b c : ℚ) : ℚ :=
  a^4+b^4+c^4-a^2*b^2-a^2*c^2-b^2*c^2

def heron (a b c : ℚ) : ℚ :=
  2*a^2*b^2+2*a^2*c^2+2*b^2*c^2-a^4-b^4-c^4

def crossA (k z w : ℚ) : ℚ := (k+z-w)/4
def crossB (k z w : ℚ) : ℚ := (k+z+w)/4
def crossC (k z : ℚ) : ℚ := (k-z)/2

def sideA (v : ℚ) : ℚ := (1+v)/2
def sideB (v : ℚ) : ℚ := (1-v)/2

lemma orbit_equations {k z v w : ℚ} (hk : k ≠ 0) (hz : z ≠ 0)
    (hc : v^2*(3*k*z+1) = 3*k*z*(z^2-k*z+k^2-1))
    (hw : 3*k*z*w^2 = 3*k*z*(k-z)^2-4*v^2) :
    crossA k z w ^ 2+crossB k z w ^ 2+crossC k z ^ 2 =
        sideA v ^ 2+sideB v ^ 2 ∧
      delta (crossA k z w) (crossB k z w) (crossC k z) = sideA v ^ 2*sideB v ^ 2 := by
  have hn : 3*k*z ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hk) hz
  have hs : crossA k z w ^ 2+crossB k z w ^ 2+crossC k z ^ 2 =
      sideA v ^ 2+sideB v ^ 2 := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show (3*k*z)*
      (crossA k z w ^ 2+crossB k z w ^ 2+crossC k z ^ 2-
        (sideA v ^ 2+sideB v ^ 2)) = 0 from ?_)).resolve_left hn
    dsimp [crossA,crossB,crossC,sideA,sideB]
    linear_combination hw/8-hc/2
  have hh : 3*heron (crossA k z w) (crossB k z w) (crossC k z) = v^2 := by
    dsimp [heron,crossA,crossB,crossC]
    linear_combination -hw/4
  refine ⟨hs,?_⟩
  have hid : (crossA k z w ^ 2+crossB k z w ^ 2+crossC k z ^ 2)^2-
      4*delta (crossA k z w) (crossB k z w) (crossC k z) =
        3*heron (crossA k z w) (crossB k z w) (crossC k z) := by
    dsimp [delta,heron]
    ring
  rw [hs,hh] at hid
  have hab : (sideA v ^ 2+sideB v ^ 2)^2-4*(sideA v ^ 2*sideB v ^ 2) = v^2 := by
    dsimp [sideA,sideB]
    ring
  linarith [hid,hab]

def scale (k : ℚ) : ℚ := 3*k*(k^2-1)

def ellipticPolynomial (k X : ℚ) : ℚ :=
  X^3+3*k^2*(3*k^2-4)*X^2+9*k^2*(1-3*k^2)*(k^2-1)*X+
    81*k^4*(k^2-1)^2

lemma elliptic_factorization (k X : ℚ) :
    ellipticPolynomial k X =
      (X+3*k*scale k)*(X^2-3*k^2*X+3*k*scale k) := by
  dsimp [ellipticPolynomial,scale]
  ring

def quotientZ (k X : ℚ) : ℚ := scale k/X

def quotientV (k X Y : ℚ) : ℚ := Y*scale k/(X*(X+3*k*scale k))

lemma elliptic_quartic_identity {k X Y : ℚ}
    (hX : X ≠ 0) (hT : X+3*k*scale k ≠ 0) :
    quotientV k X Y ^ 2*(3*k*quotientZ k X+1)-
      3*k*quotientZ k X*(quotientZ k X^2-k*quotientZ k X+k^2-1) =
        scale k^2*(Y^2-ellipticPolynomial k X)/(X^3*(X+3*k*scale k)) := by
  dsimp only [quotientV,quotientZ]
  generalize he : X+3*k*scale k = T at *
  field_simp [hX,hT]
  subst T
  dsimp [ellipticPolynomial,scale]
  ring

lemma elliptic_to_quartic {k X Y : ℚ}
    (hX : X ≠ 0) (hT : X+3*k*scale k ≠ 0)
    (hE : Y^2 = ellipticPolynomial k X) :
    quotientV k X Y ^ 2*(3*k*quotientZ k X+1) =
      3*k*quotientZ k X*(quotientZ k X^2-k*quotientZ k X+k^2-1) := by
  have h := elliptic_quartic_identity (Y := Y) hX hT
  rw [hE,sub_self,mul_zero,zero_div] at h
  exact sub_eq_zero.mp h

/-- The remaining square condition really lifts a point of the elliptic
quotient to the orbit-pair equations. It is not automatic. -/
lemma elliptic_lift {k X Y : ℚ} (hk : k ≠ 0) (hL : scale k ≠ 0)
    (hX : X ≠ 0) (hT : X+3*k*scale k ≠ 0)
    (hE : Y^2 = ellipticPolynomial k X)
    (hD : IsSquare ((k-quotientZ k X)^2-
      4*quotientV k X Y ^ 2/(3*k*quotientZ k X))) :
    ∃ w : ℚ,
      crossA k (quotientZ k X) w ^ 2+crossB k (quotientZ k X) w ^ 2+
          crossC k (quotientZ k X) ^ 2 =
            sideA (quotientV k X Y) ^ 2+sideB (quotientV k X Y) ^ 2 ∧
      delta (crossA k (quotientZ k X) w) (crossB k (quotientZ k X) w)
        (crossC k (quotientZ k X)) =
          sideA (quotientV k X Y) ^ 2*sideB (quotientV k X Y) ^ 2 := by
  have hz : quotientZ k X ≠ 0 := div_ne_zero hL hX
  obtain ⟨w,hw⟩ := hD
  refine ⟨w,orbit_equations hk hz (elliptic_to_quartic hX hT hE) ?_⟩
  have hden : 3*k*quotientZ k X ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hk) hz
  field_simp at hw
  nlinarith [hw]

#print axioms orbit_equations
#print axioms elliptic_to_quartic
#print axioms elliptic_lift

end Erdos213.ThreefoldElliptic
