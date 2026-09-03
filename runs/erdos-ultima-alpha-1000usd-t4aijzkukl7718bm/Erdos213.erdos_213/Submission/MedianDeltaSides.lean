import Mathlib.Tactic

/-! A rational parametrization of the side/discriminant conditions in the
conditional median construction. The median squares are NOT automatic.
This file does not prove or disprove Erdős 213. -/
namespace Erdos213.MedianDeltaSides

variable {R : Type*} [CommRing R]

def baseU (s : R) : R := s^2-1
def baseV (s : R) : R := 2*s-1
def denom (s k : R) : R := k^2*baseV s-baseU s
def numA (s k : R) : R := (2*k-1)*baseU s-k^2*baseV s
def numC (s k : R) : R := baseU s+(k^2-2*k)*baseV s
def numQ (s k : R) : R := 4*k*(k-1)*(baseU s-k*baseV s)

def delta (a b c : R) : R := a^4+b^4+c^4-a^2*b^2-a^2*c^2-b^2*c^2
def heron (a b c : R) : R := 2*a^2*b^2+2*a^2*c^2+2*b^2*c^2-a^4-b^4-c^4

def median₁ (a b c : R) : R := 2*a^2+2*b^2-c^2
def median₂ (a b c : R) : R := 2*a^2-b^2+2*c^2
def median₃ (a b c : R) : R := -a^2+2*b^2+2*c^2

lemma side_identities (s k : R) :
    (numA s k)^2-(denom s k)^2=numQ s k*baseU s ∧
    (numC s k)^2-(denom s k)^2=numQ s k*baseV s := by
  dsimp [numA,numC,denom,numQ,baseU,baseV]
  constructor <;> ring

lemma discriminant_identity (s k : R) :
    delta (numA s k) (denom s k) (numC s k) =
      (numQ s k*(s^2-s+1))^2 := by
  dsimp [delta,numA,numC,denom,numQ,baseU,baseV]
  ring

lemma heron_identity (s k : R) :
    heron (numA s k) (denom s k) (numC s k) =
      ((denom s k)^2+numQ s k*s^2)*
      (3*(denom s k)^2-numQ s k*(s-2)^2) := by
  dsimp [heron,numA,numC,denom,numQ,baseU,baseV]
  ring

lemma heron_linear_factors (s k : R) :
    heron (numA s k) (denom s k) (numC s k) =
      -(((2*k-1)*s-(k+1))*((2*k-1)*s-(k-1))*
      ((2*k+1)*s-(k-1))*((2*k-3)*s-(k-3))*
      (s-3*k+1)*(s-k-1)*(s-k+1)*(s+k-1)) := by
  dsimp [heron,numA,numC,denom,baseU,baseV]
  ring

/-- The square discriminant is automatic, without imposing median squares. -/
lemma square_discriminant (s k : ℚ) :
    IsSquare (delta (numA s k) (denom s k) (numC s k)) := by
  rw [discriminant_identity]
  exact IsSquare.sq _

lemma rational_side_identities (s k : ℚ) (hd : denom s k ≠ 0) :
    (numA s k/denom s k)^2 = 1+(numQ s k/(denom s k)^2)*baseU s ∧
    (numC s k/denom s k)^2 = 1+(numQ s k/(denom s k)^2)*baseV s := by
  obtain ⟨ha,hc⟩ := side_identities s k
  constructor <;> field_simp <;> nlinarith

/-- A positive-area control. This triangle does NOT have rational medians. -/
lemma triangle_control :
    delta (19 : ℚ) 13 17=168^2 ∧ heron (19 : ℚ) 13 17=185955 ∧
    median₁ (19 : ℚ) 13 17=771 ∧ median₂ (19 : ℚ) 13 17=1131 ∧
    median₃ (19 : ℚ) 13 17=555 := by
  norm_num [delta,heron,median₁,median₂,median₃]


lemma control_coordinates :
    numA (3 : ℚ) (3/2)=19/4 ∧ denom (3 : ℚ) (3/2)=13/4 ∧
    numC (3 : ℚ) (3/2)=17/4 := by
  norm_num [numA,numC,denom,baseU,baseV]

lemma control_medians_not_square :
    ¬IsSquare (771 : ℚ) ∧ ¬IsSquare (1131 : ℚ) ∧ ¬IsSquare (555 : ℚ) := by
  decide +kernel

lemma three_mul_sq_not_square (x : ℚ) (hx : x ≠ 0) :
    ¬IsSquare (3*x^2) := by
  rintro ⟨y,hy⟩
  have h3 : ¬IsSquare (3 : ℚ) := by decide +kernel
  apply h3
  refine ⟨y/x, ?_⟩
  field_simp
  nlinarith [hy]

lemma equilateral_fibers (s k : ℚ) (hk : k=0 ∨ k=1) (hd : denom s k ≠ 0) :
    ¬IsSquare (median₁ (numA s k) (denom s k) (numC s k)) := by
  have he : median₁ (numA s k) (denom s k) (numC s k) = 3*(denom s k)^2 := by
    rcases hk with rfl | rfl <;> dsimp [median₁,numA,numC,denom,baseU,baseV] <;> ring
  rw [he]
  exact three_mul_sq_not_square _ hd


#print axioms side_identities
#print axioms discriminant_identity
#print axioms heron_identity
#print axioms heron_linear_factors
#print axioms square_discriminant
#print axioms rational_side_identities
#print axioms triangle_control
#print axioms control_coordinates
#print axioms control_medians_not_square
#print axioms three_mul_sq_not_square
#print axioms equilateral_fibers

end Erdos213.MedianDeltaSides
