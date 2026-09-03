import Submission.IsoscelesCurve
import Submission.MedianDeltaSides

/-! Necessary rational specializations for the side/discriminant map.
These are not an existence theorem for a rational-function section. -/
namespace Erdos213.MedianSpecialization
open MedianDeltaSides
set_option maxHeartbeats 1000000

def AllMedians (a b c : ℚ) : Prop :=
  IsSquare (2*b^2+2*c^2-a^2) ∧ IsSquare (2*a^2+2*c^2-b^2) ∧
    IsSquare (2*a^2+2*b^2-c^2)

def SectionPoint (s k : ℚ) : Prop := AllMedians (numA s k) (denom s k) (numC s k)

lemma equal_sq_heron {a b c : ℚ} (h : AllMedians a b c)
    (he : a^2=b^2 ∨ a^2=c^2 ∨ b^2=c^2) : heron a b c=0 := by
  rcases he with he | he | he
  · exact IsoscelesCurve.isosceles_heron_zero he h.1 h.2.2
  · have h₁ : IsSquare (2*c^2+2*b^2-a^2) := by convert h.1 using 1 <;> ring
    have hh := IsoscelesCurve.isosceles_heron_zero he h₁ h.2.1
    dsimp [heron]
    linear_combination hh
  · have h₁ : IsSquare (2*c^2+2*a^2-b^2) := by convert h.2.1 using 1 <;> ring
    have hh := IsoscelesCurve.isosceles_heron_zero he h₁ h.1
    dsimp [heron]
    linear_combination hh

lemma pm_one_values {s k : ℚ} (hs : s=1 ∨ s= -1) (h : SectionPoint s k) :
    k=0 ∨ k=2 ∨ k=2/3 ∨ k= -2 := by
  have hab : (numA s k)^2=(denom s k)^2 := by
    rcases hs with rfl | rfl <;> dsimp [numA,denom,baseU,baseV] <;> ring
  have hh := equal_sq_heron h (Or.inl hab)
  have hf : k^4*(k-2)^2*(k+2)*(3*k-2)=0 := by
    rcases hs with rfl | rfl
    · dsimp [heron,numA,denom,numC,baseU,baseV] at hh
      linear_combination hh
    · dsimp [heron,numA,denom,numC,baseU,baseV] at hh
      linear_combination hh/81
  simp only [mul_eq_zero,pow_eq_zero_iff (by decide : 4≠0),
    pow_eq_zero_iff (by decide : 2≠0)] at hf
  rcases hf with ((h | h) | h) | h
  · exact Or.inl h
  · right; left; linarith
  · right; right; right; linarith
  · right; right; left; linarith

lemma zero_two_values {s k : ℚ} (hs : s=0 ∨ s=2) (h : SectionPoint s k) :
    k=1 ∨ k= -1 ∨ k=3 ∨ k=1/3 := by
  have hab : (numA s k)^2=(numC s k)^2 := by
    rcases hs with rfl | rfl <;> dsimp [numA,numC,baseU,baseV] <;> ring
  have hh := equal_sq_heron h (Or.inr (Or.inl hab))
  have hf : (k-3)*(k-1)^4*(k+1)^2*(3*k-1)=0 := by
    rcases hs with rfl | rfl
    · dsimp [heron,numA,denom,numC,baseU,baseV] at hh
      linear_combination hh
    · dsimp [heron,numA,denom,numC,baseU,baseV] at hh
      linear_combination hh/81
  simp only [mul_eq_zero,pow_eq_zero_iff (by decide : 4≠0),
    pow_eq_zero_iff (by decide : 2≠0)] at hf
  rcases hf with ((h | h) | h) | h
  · right; right; left; linarith
  · left; linarith
  · right; left; linarith
  · right; right; right; linarith

lemma half_values {k : ℚ} (h : SectionPoint (1/2) k) :
    k=1/2 ∨ k= -1/2 ∨ k=3/2 := by
  have hab : (denom (1/2 : ℚ) k)^2=(numC (1/2 : ℚ) k)^2 := by
    dsimp [denom,numC,baseU,baseV]
    ring
  have hh := equal_sq_heron h (Or.inr (Or.inr hab))
  have hf : (2*k-3)*(2*k-1)^2*(2*k+1)=0 := by
    dsimp [heron,numA,denom,numC,baseU,baseV] at hh
    linear_combination (-256/81 : ℚ)*hh
  simp only [mul_eq_zero,pow_eq_zero_iff (by decide : 2≠0)] at hf
  rcases hf with (h | h) | h
  · right; right; linarith
  · left; linarith
  · right; left; linarith

lemma infinity_finite_values {k : ℚ} (h : AllMedians (2*k-1) (-1) 1) :
    k=1/2 ∨ k= -1/2 ∨ k=3/2 := by
  have hh := equal_sq_heron h (Or.inr (Or.inr (by norm_num)))
  have hf : (2*k-3)*(2*k-1)^2*(2*k+1)=0 := by
    dsimp [heron] at hh
    linear_combination -hh
  simp only [mul_eq_zero,pow_eq_zero_iff (by decide : 2≠0)] at hf
  rcases hf with (h | h) | h
  · right; right; linarith
  · left; linarith
  · right; left; linarith

lemma infinity_linear_values {k : ℚ} (hk : k≠0)
    (h : AllMedians (2*k-2*k^2) (2*k^2) (2*k^2)) :
    k=1 ∨ k=1/3 ∨ k= -1 := by
  have hh := equal_sq_heron h (Or.inr (Or.inr rfl))
  have hf : k^4*(k-1)^2*(3*k-1)*(k+1)=0 := by
    dsimp [heron] at hh
    linear_combination hh/16
  simp only [mul_eq_zero,pow_eq_zero_iff (by decide : 4≠0),
    pow_eq_zero_iff (by decide : 2≠0)] at hf
  rcases hf with ((h | h) | h) | h
  · exact False.elim (hk h)
  · left; linarith
  · right; left; linarith
  · right; right; linarith

lemma equilateral_leading_zero {a : ℚ} (h : AllMedians (-a) a a) : a=0 := by
  have hh := equal_sq_heron h (Or.inr (Or.inr rfl))
  have hf : a^4=0 := by
    dsimp [heron] at hh
    nlinarith only [hh]
  exact (pow_eq_zero_iff (by decide : 4≠0)).mp hf

#print axioms infinity_finite_values
#print axioms infinity_linear_values
#print axioms equilateral_leading_zero
#print axioms equal_sq_heron
#print axioms pm_one_values
#print axioms zero_two_values
#print axioms half_values
end Erdos213.MedianSpecialization
