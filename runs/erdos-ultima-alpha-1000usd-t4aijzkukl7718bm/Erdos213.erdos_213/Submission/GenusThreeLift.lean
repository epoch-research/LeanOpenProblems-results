import FormalConjecturesUtil

set_option linter.unnecessarySeqFocus false

/-! The norm-square condition permits a rational quadratic twist; it is
strictly weaker than requiring a square in a fixed quadratic field. This is
an algebraic reduction, not an eight-point existence theorem. -/

namespace Erdos213.GenusThreeLift
open QuadraticAlgebra
noncomputable section

private lemma lift_from_norm_root {K : Type*} [Field K] [CharZero K]
    {a : K} (z : QuadraticAlgebra K a 0) (r : K)
    (hr : QuadraticAlgebra.norm z = r*r) (hs : z.re+r ≠ 0) :
    ∃ δ : K, δ ≠ 0 ∧ IsSquare (algebraMap K (QuadraticAlgebra K a 0) δ*z) := by
  refine ⟨2*(z.re+r), mul_ne_zero (by norm_num) hs, z+algebraMap K _ r, ?_⟩
  simp only [norm_def, zero_mul] at hr
  ext
  · simp
    linear_combination hr
  · simp
    ring

lemma norm_square_iff_twisted_square {K : Type*} [Field K] [CharZero K]
    {a : K} (z : QuadraticAlgebra K a 0) (hn : QuadraticAlgebra.norm z ≠ 0) :
    IsSquare (QuadraticAlgebra.norm z) ↔
      ∃ δ : K, δ ≠ 0 ∧ IsSquare (algebraMap K (QuadraticAlgebra K a 0) δ*z) := by
  constructor
  · rintro ⟨r,hr⟩
    have hr0 : r ≠ 0 := by intro h; apply hn; simp [hr,h]
    by_cases hs : z.re+r ≠ 0
    · exact lift_from_norm_root z r hr hs
    · have he : z.re+r = 0 := not_ne_iff.mp hs
      apply lift_from_norm_root z (-r) (by simpa using hr)
      intro hz
      have hh : (2 : K)*r = 0 := by linear_combination he-hz
      exact (mul_ne_zero (by norm_num) hr0) hh
  · rintro ⟨δ,hδ,v,hv⟩
    have hnorm := congrArg QuadraticAlgebra.norm hv
    simp only [map_mul, QuadraticAlgebra.norm_algebraMap] at hnorm
    refine ⟨QuadraticAlgebra.norm v/δ, ?_⟩
    field_simp
    linear_combination hnorm

/-- Even a nonzero element of norm a rational square need not be a square
in the quadratic field itself. -/
lemma norm_square_does_not_imply_square :
    IsSquare (QuadraticAlgebra.norm (algebraMap ℚ (QuadraticAlgebra ℚ (-3) 0) 2)) ∧
    ¬ IsSquare (algebraMap ℚ (QuadraticAlgebra ℚ (-3) 0) 2) := by
  constructor
  · rw [QuadraticAlgebra.norm_algebraMap]
    exact ⟨2, by ring⟩
  · rintro ⟨v,hv⟩
    have hr := congrArg QuadraticAlgebra.re hv
    have hi := congrArg QuadraticAlgebra.im hv
    simp at hr hi
    have hh : v.re*v.im = 0 := by linarith
    rcases mul_eq_zero.mp hh with hx | hy
    · rw [hx] at hr
      nlinarith [sq_nonneg v.im]
    · have hs : IsSquare (2 : ℚ) := ⟨v.re, by simpa [hy] using hr⟩
      norm_num at hs

abbrev ParameterAlgebra (b c : ℚ) := QuadraticAlgebra ℚ (b^2-4*c) 0

def parameter (b c : ℚ) : ParameterAlgebra b c := ⟨-b/2, 1/2⟩

def branchValue (b c : ℚ) : ParameterAlgebra b c :=
  let z := parameter b c
  z*(z-1)*(z+1)*(z-3)*(z+3)*(z^2+3)

def SquareConditions (b c : ℚ) : Prop :=
  IsSquare c ∧ IsSquare (1+b+c) ∧ IsSquare (1-b+c) ∧
    IsSquare (9+3*b+c) ∧ IsSquare (9-3*b+c) ∧ IsSquare ((c-3)^2+3*b^2)

lemma parameter_equation (b c : ℚ) :
    parameter b c ^ 2 + algebraMap ℚ _ b*parameter b c + algebraMap ℚ _ c = 0 := by
  ext <;> simp [parameter, pow_two] <;> ring

lemma parameter_norm (b c : ℚ) : QuadraticAlgebra.norm (parameter b c) = c := by
  simp [parameter, norm_def]
  ring

lemma shifted_parameter_norm (b c r : ℚ) :
    QuadraticAlgebra.norm (parameter b c-algebraMap ℚ _ r) = r^2+b*r+c := by
  simp [parameter, norm_def]
  ring

lemma extra_parameter_norm (b c : ℚ) :
    QuadraticAlgebra.norm (parameter b c ^ 2+3) = (c-3)^2+3*b^2 := by
  simp [parameter, norm_def, pow_two]
  ring

lemma branchValue_norm (b c : ℚ) :
    QuadraticAlgebra.norm (branchValue b c) =
      c*(1-b+c)*(1+b+c)*(9-3*b+c)*(9+3*b+c)*((c-3)^2+3*b^2) := by
  dsimp only [branchValue]
  simp only [map_mul, parameter_norm, extra_parameter_norm]
  have h1 : QuadraticAlgebra.norm (parameter b c-1) = 1+b+c := by
    simpa using shifted_parameter_norm b c 1
  have hm1 : QuadraticAlgebra.norm (parameter b c+1) = 1-b+c := by
    simpa [sub_eq_add_neg] using shifted_parameter_norm b c (-1)
  have h3 : QuadraticAlgebra.norm (parameter b c-3) = 9+3*b+c := by
    convert shifted_parameter_norm b c 3 using 1 <;> norm_num <;> ring
  have hm3 : QuadraticAlgebra.norm (parameter b c+3) = 9-3*b+c := by
    have hh := shifted_parameter_norm b c (-3)
    have hc : algebraMap ℚ (ParameterAlgebra b c) (-3) = -(3 : ParameterAlgebra b c) := by
      simp only [map_neg, map_ofNat]
    rw [hc, sub_neg_eq_add] at hh
    convert hh using 1 <;> norm_num <;> ring
  rw [h1,hm1,h3,hm3]
  ring

lemma branchValue_norm_square {b c : ℚ} (h : SquareConditions b c) :
    IsSquare (QuadraticAlgebra.norm (branchValue b c)) := by
  rw [branchValue_norm]
  exact ((((h.1.mul h.2.2.1).mul h.2.1).mul h.2.2.2.2.1).mul h.2.2.2.1).mul h.2.2.2.2.2

lemma branchValue_norm_pos {b c : ℚ} (h : SquareConditions b c) (hd : b^2 < 4*c) :
    0 < QuadraticAlgebra.norm (branchValue b c) := by
  have hq (r : ℚ) : 0 < r^2+b*r+c := by nlinarith [sq_nonneg (2*r+b)]
  have hc : c ≠ 3 := by intro he; have hh := h.1; rw [he] at hh; norm_num at hh
  have he : 0 < (c-3)^2+3*b^2 := by
    have hh : 0 < (c-3)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hc)
    nlinarith [sq_nonneg b]
  have h0 : 0 < c := by nlinarith [hq 0]
  have h1 : 0 < 1+b+c := by nlinarith [hq 1]
  have hm1 : 0 < 1-b+c := by nlinarith [hq (-1)]
  have h3 : 0 < 9+3*b+c := by nlinarith [hq 3]
  have hm3 : 0 < 9-3*b+c := by nlinarith [hq (-3)]
  rw [branchValue_norm]
  positivity

/-- Every nonreal parameter meeting the SIX norm conditions lifts to a point
on some rational quadratic twist of the genus-three curve. This does not
require its divisor class to belong to twice the Jacobian. -/
theorem exists_genus_three_twist {b c : ℚ} (h : SquareConditions b c)
    (hd : b^2 < 4*c) :
    ∃ δ : ℚ, δ ≠ 0 ∧ ∃ v : ParameterAlgebra b c,
      v^2 = algebraMap ℚ _ δ*branchValue b c := by
  obtain ⟨δ,hδ,v,hv⟩ := (norm_square_iff_twisted_square (branchValue b c)
    (ne_of_gt (branchValue_norm_pos h hd))).mp (branchValue_norm_square h)
  exact ⟨δ,hδ,v, by simpa only [pow_two] using hv.symm⟩


def BranchSquareConditions (b c : ℚ) : Prop :=
  IsSquare c ∧ IsSquare (1+b+c) ∧ IsSquare (1-b+c) ∧
    IsSquare (9+3*b+c) ∧ IsSquare (9-3*b+c)

/-- The five real-branch square conditions plus a point on some quadratic
twist are exactly the six norm conditions. No divisibility-by-two condition
on a Jacobian is included in this equivalence. -/
theorem square_conditions_iff_twist {b c : ℚ} (hd : b^2 < 4*c) :
    SquareConditions b c ↔ BranchSquareConditions b c ∧
      ∃ δ : ℚ, δ ≠ 0 ∧ ∃ v : ParameterAlgebra b c,
        v^2 = algebraMap ℚ _ δ*branchValue b c := by
  constructor
  · intro h
    exact ⟨⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩, exists_genus_three_twist h hd⟩
  · rintro ⟨h,δ,hδ,v,hv⟩
    have hn := congrArg QuadraticAlgebra.norm hv
    simp only [map_pow, map_mul, QuadraticAlgebra.norm_algebraMap] at hn
    have hN : IsSquare (QuadraticAlgebra.norm (branchValue b c)) := by
      refine ⟨QuadraticAlgebra.norm v/δ, ?_⟩
      field_simp
      linear_combination -hn
    let P : ℚ := c*(1-b+c)*(1+b+c)*(9-3*b+c)*(9+3*b+c)
    have hP : IsSquare P := (((h.1.mul h.2.2.1).mul h.2.1).mul h.2.2.2.2).mul h.2.2.2.1
    have hq (r : ℚ) : 0 < r^2+b*r+c := by nlinarith [sq_nonneg (2*r+b)]
    have h0 : 0 < c := by nlinarith [hq 0]
    have h1 : 0 < 1+b+c := by nlinarith [hq 1]
    have hm1 : 0 < 1-b+c := by nlinarith [hq (-1)]
    have h3 : 0 < 9+3*b+c := by nlinarith [hq 3]
    have hm3 : 0 < 9-3*b+c := by nlinarith [hq (-3)]
    have hP0 : P ≠ 0 := ne_of_gt (by dsimp [P]; positivity)
    have he : IsSquare ((c-3)^2+3*b^2) := by
      have hh := hN.div hP
      rw [branchValue_norm] at hh
      change IsSquare ((P*((c-3)^2+3*b^2))/P) at hh
      simpa [hP0] using hh
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,he⟩

lemma parameter_nonsquare {b c : ℚ} (hd : b^2 < 4*c) :
    ∀ r : ℚ, r^2 ≠ b^2-4*c+0*r := by
  intro r h
  nlinarith [sq_nonneg r]

lemma conic_parameter_identity {s : ℚ} (hs : s ≠ 0) :
    ((s^2-3)/(2*s))^2+3 = ((s^2+3)/(2*s))^2 := by
  field_simp
  ring

#print axioms square_conditions_iff_twist
#print axioms parameter_nonsquare
#print axioms conic_parameter_identity

#print axioms norm_square_iff_twisted_square
#print axioms norm_square_does_not_imply_square
#print axioms exists_genus_three_twist

end
end Erdos213.GenusThreeLift
