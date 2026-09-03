import FormalConjecturesUtil

/-! Arithmetic of a conditional eight-point construction. No existence theorem
for eight points, and no assertion about arbitrary cardinalities, is made here. -/

namespace Erdos213.PythagoreanFibration

def quadNorm (b c x s : ℚ) : ℚ :=
  s^2+b^2*s+c^2+2*b*s*x+2*b*c*x+c*(4*x^2-2*s)

lemma quadNorm_cone (b c x s : ℚ) :
    quadNorm b c x s = (s+b*x+b^2/2-c)^2+(4*c-b^2)*(x+b/2)^2 := by
  unfold quadNorm
  ring

/-- A rational line pencil imposing one quadratic norm condition. -/
lemma quadNorm_line_square (b c u x : ℚ) (hu : u≠0) :
    let k := (u^2-(4*c-b^2))/(2*u)
    quadNorm b c x ((k-b)*(x+b/2)+c) =
      (((u^2+(4*c-b^2))/(2*u))*(x+b/2))^2 := by
  dsimp
  rw [quadNorm_cone]
  field_simp
  ring

def values (x s : ℚ) : Fin 6 → ℚ :=
  ![s, s-2*x+1, s+2*x+1, (s-1)^2+4*x^2,
    s^2+6*s+1-4*x^2-4*x*(s-1), s^2+6*s+1-4*x^2+4*x*(s-1)]

lemma quadratic_values (x s : ℚ) :
    values x s 3 = quadNorm 0 1 x s ∧
    values x s 4 = quadNorm (-2) (-1) x s ∧
    values x s 5 = quadNorm 2 (-1) x s := by
  dsimp [values,quadNorm]
  exact ⟨by ring,by ring,by ring⟩

lemma first_fibration (r a : ℚ) (hr : 1-r^2≠0) :
    let x := r*(1-a^2)/(1-r^2)
    let h := 2*r/(1-r^2)
    values x (a^2) 1 = (1-h)+(1+h)*a^2 ∧
    values x (a^2) 2 = (1+h)+(1-h)*a^2 ∧
    values x (a^2) 3 = ((1+r^2)*(1-a^2)/(1-r^2))^2 ∧
    a^2-x^2 = (a^2-r^2)*(1-a^2*r^2)/(1-r^2)^2 := by
  dsimp [values]
  constructor
  · ring
  constructor
  · ring
  constructor
  · field_simp; ring
  · field_simp; ring

lemma first_fibration_extra (r a : ℚ) :
    let x := r*(1-a^2)/(1-r^2)
    let h := 2*r/(1-r^2)
    values x (a^2) 4 = 8*a^2+(1-h^2+2*h)*(a^2-1)^2 ∧
    values x (a^2) 5 = 8*a^2+(1-h^2-2*h)*(a^2-1)^2 := by
  dsimp [values]
  constructor <;> ring

/-- Away from two symmetry loci, every square value of the fourth norm
belongs to this rational line pencil. This is not a classification of its
rational points after imposing the other five norm conditions. -/
lemma first_fibration_covers {x s : ℚ} (hx : x≠0) (hs : s≠1)
    (hq : IsSquare (values x s 3)) :
    ∃ r : ℚ, r≠0 ∧ 1-r^2≠0 ∧ x=r*(1-s)/(1-r^2) := by
  obtain ⟨c,hc⟩ := hq
  have hc' : c^2=(s-1)^2+4*x^2 := by
    dsimp [values] at hc
    nlinarith
  let r : ℚ := (s-1+c)/(2*x)
  have he : x*r^2+(1-s)*r-x=0 := by
    dsimp [r]
    field_simp
    linear_combination hc'
  have hr : r≠0 := by
    intro hr
    rw [hr] at he
    apply hx
    nlinarith
  have hd : 1-r^2≠0 := by
    intro hd
    have hprod : (1-s)*r=0 := by
      linear_combination he + x * hd
    have hh := (mul_eq_zero.mp hprod).resolve_right hr
    apply hs
    linarith
  refine ⟨r,hr,hd,?_⟩
  apply (eq_div_iff hd).mpr
  nlinarith

lemma rotation_values (x s : ℚ) (hd : s+2*x+1≠0) :
    values ((s-1)/(s+2*x+1)) ((s-2*x+1)/(s+2*x+1)) =
      ![values x s 1 / values x s 2, 4 / values x s 2,
        4*values x s 0 / values x s 2,
        4*values x s 3 / (values x s 2)^2,
        4*values x s 5 / (values x s 2)^2,
        4*values x s 4 / (values x s 2)^2] := by
  funext i
  fin_cases i <;> dsimp [values] <;> field_simp <;> ring

lemma rotation_preserves_squares (x s : ℚ) (hd : s+2*x+1≠0)
    (hs : ∀ i, IsSquare (values x s i)) :
    ∀ i, IsSquare (values ((s-1)/(s+2*x+1)) ((s-2*x+1)/(s+2*x+1)) i) := by
  rw [rotation_values x s hd]
  intro i
  have h4 : IsSquare (4 : ℚ) := by norm_num
  fin_cases i
  · exact (hs 1).div (hs 2)
  · exact h4.div (hs 2)
  · exact (h4.mul (hs 0)).div (hs 2)
  · exact (h4.mul (hs 3)).div (IsSquare.pow 2 (hs 2))
  · exact (h4.mul (hs 5)).div (IsSquare.pow 2 (hs 2))
  · exact (h4.mul (hs 4)).div (IsSquare.pow 2 (hs 2))

lemma rotation_area (x s : ℚ) (hd : s+2*x+1≠0) :
    (s-2*x+1)/(s+2*x+1)-((s-1)/(s+2*x+1))^2 =
      4*(s-x^2)/(s+2*x+1)^2 := by
  field_simp
  ring

lemma two_symmetry_lines_excluded (x s : ℚ) (hs : ∀ i, IsSquare (values x s i)) :
    s+2*x≠1 ∧ s-2*x≠1 := by
  constructor
  · intro he
    have hh : IsSquare (2 : ℚ) := by
      convert hs 2 using 1
      dsimp [values]
      linarith
    norm_num at hh
  · intro he
    have hh : IsSquare (2 : ℚ) := by
      convert hs 1 using 1
      dsimp [values]
      linarith
    norm_num at hh

#print axioms quadNorm_line_square
#print axioms first_fibration
#print axioms first_fibration_covers
#print axioms rotation_preserves_squares
#print axioms two_symmetry_lines_excluded

end Erdos213.PythagoreanFibration
