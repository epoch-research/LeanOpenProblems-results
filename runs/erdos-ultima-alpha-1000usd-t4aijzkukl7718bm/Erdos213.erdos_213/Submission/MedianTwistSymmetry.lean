import Submission.MedianHalvingQuartics

/-! Algebraic normalization and symmetries of the congruent-six median twist.
No rank or rational-point completeness statement is asserted here. -/
namespace Erdos213.MedianTwistSymmetry
set_option maxHeartbeats 2000000

def base (r : ℚ) : ℚ := r*(r^2-1)
def parameter (r : ℚ) : ℚ := 3*(r^2+1)^2/(8*base r)

def TwistEquation (r x y : ℚ) : Prop :=
  6*base r*y^2 = x^3+9*(r^2+1)^2*x^2-576*(base r)^2*x

def UniversalEquation (l z w : ℚ) : Prop := w^2=z^3+l*z^2-z

lemma normalized_twist {r x y : ℚ} (hr : base r ≠ 0) :
    TwistEquation r x y ↔
      UniversalEquation (parameter r) (x/(24*base r)) (y/(48*base r)) := by
  unfold TwistEquation UniversalEquation parameter
  constructor
  · intro h
    field_simp
    linear_combination 18432*h
  · intro h
    field_simp at h
    linear_combination (1/18432 : ℚ)*h

lemma first_offset {r : ℚ} (hr : base r ≠ 0) :
    parameter r - 3/2 = 3*(r^2-2*r-1)^2/(8*base r) := by
  unfold parameter
  field_simp
  dsimp [base]
  ring

lemma second_offset {r : ℚ} (hr : base r ≠ 0) :
    parameter r + 3/2 = 3*(r^2+2*r-1)^2/(8*base r) := by
  unfold parameter
  field_simp
  dsimp [base]
  ring

lemma denominator_nonzero {r : ℚ} (hr : base r ≠ 0) :
    r ≠ 0 ∧ r-1 ≠ 0 ∧ r+1 ≠ 0 := by
  refine ⟨?_,?_,?_⟩
  · intro h; apply hr; simp [base,h]
  · intro h; have h' : r=1 := by linarith
    apply hr; simp [base,h']
  · intro h; have h' : r= -1 := by linarith
    apply hr; simp [base,h']

lemma inverse_symmetry {r : ℚ} (hr : base r ≠ 0) :
    parameter (-1/r) = parameter r := by
  obtain ⟨h₀,h₁,h₂⟩ := denominator_nonzero hr
  have hb : base (-1/r) = base r/r^4 := by
    unfold base
    field_simp
    ring
  simp only [parameter,hb]
  field_simp
  ring

lemma reflection_symmetry {r : ℚ} (hr : base r ≠ 0) :
    parameter ((1-r)/(1+r)) = parameter r := by
  obtain ⟨h₀,h₁,h₂⟩ := denominator_nonzero hr
  have h₂' : 1+r ≠ 0 := by simpa [add_comm] using h₂
  have hb : base ((1-r)/(1+r)) = 4*base r/(r+1)^4 := by
    unfold base
    field_simp
    ring
  simp only [parameter,hb]
  field_simp
  ring

lemma third_symmetry {r : ℚ} (hr : base r ≠ 0) :
    parameter ((r+1)/(r-1)) = parameter r := by
  obtain ⟨h₀,h₁,h₂⟩ := denominator_nonzero hr
  have hb : base ((r+1)/(r-1)) = 4*base r/(r-1)^4 := by
    unfold base
    field_simp
    ring
  simp only [parameter,hb]
  field_simp
  ring

/-- Three squares in arithmetic progression supplied by the base curve.
These supply individual elliptic points, not all mutual distances of a plane set. -/
lemma base_three_squares {r s : ℚ} (hr : base r ≠ 0) (hs : s^2=6*base r) :
    (3*(r^2+1)/(2*s))^2 = parameter r ∧
    (3*(r^2-2*r-1)/(2*s))^2 = parameter r - 3/2 ∧
    (3*(r^2+2*r-1)/(2*s))^2 = parameter r + 3/2 := by
  have hs₀ : s ≠ 0 := by
    intro h
    rw [h] at hs
    apply hr
    linarith
  have hb : base r = s^2/6 := by linarith
  have he (a : ℚ) : (3*a/(2*s))^2 = 3*a^2/(8*base r) := by
    rw [hb]
    field_simp
    ring
  refine ⟨he _,?_,?_⟩
  · rw [first_offset hr]
    exact he _
  · rw [second_offset hr]
    exact he _

lemma three_constant_abscissas {r s : ℚ} (hr : base r ≠ 0)
    (hs : s^2=6*base r) :
    UniversalEquation (parameter r) 1 (3*(r^2+1)/(2*s)) ∧
    UniversalEquation (parameter r) (-2) (3*(r^2-2*r-1)/s) ∧
    UniversalEquation (parameter r) 2 (3*(r^2+2*r-1)/s) := by
  obtain ⟨h₁,h₂,h₃⟩ := base_three_squares hr hs
  unfold UniversalEquation
  have h₂' : 3*(r^2-2*r-1)/s = 2*(3*(r^2-2*r-1)/(2*s)) := by ring
  have h₃' : 3*(r^2+2*r-1)/s = 2*(3*(r^2+2*r-1)/(2*s)) := by ring
  rw [h₂',h₃']
  constructor
  · nlinarith only [h₁]
  constructor
  · nlinarith only [h₂]
  · nlinarith only [h₃]


/-- The three constant abscissas pull back to polynomial sections already
rational over the original base, not to new independent base-change sections. -/
lemma original_polynomial_sections (r : ℚ) :
    (72*base r*(r^2+1))^2 =
      (24*base r)^3 + 9*(r^2+1)^2*(24*base r)^2 - 576*(base r)^2*(24*base r) ∧
    (144*base r*(r^2+2*r-1))^2 =
      (48*base r)^3 + 9*(r^2+1)^2*(48*base r)^2 - 576*(base r)^2*(48*base r) ∧
    (144*base r*(r^2-2*r-1))^2 =
      (-48*base r)^3 + 9*(r^2+1)^2*(-48*base r)^2 - 576*(base r)^2*(-48*base r) := by
  dsimp [base]
  constructor
  · ring
  constructor <;> ring


#print axioms normalized_twist
#print axioms inverse_symmetry
#print axioms original_polynomial_sections
#print axioms reflection_symmetry
#print axioms third_symmetry
#print axioms base_three_squares
#print axioms three_constant_abscissas
end Erdos213.MedianTwistSymmetry
