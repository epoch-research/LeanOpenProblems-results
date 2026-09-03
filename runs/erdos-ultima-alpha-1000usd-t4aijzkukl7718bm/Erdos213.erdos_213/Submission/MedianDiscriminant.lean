import Submission.RationalThreeSquares
import Mathlib.Tactic
import Mathlib.Algebra.Order.Field.Basic

/-!
Exact arithmetic reformulation for the discriminant-first median template.
These statements are conditional arithmetic identities, not a solution of
Erdős 213 and not an assertion of general position for a geometric template.
-/

namespace Erdos213.MedianDiscriminant

def delta (A C : ℚ) : ℚ := A^2 + 1 + C^2 - A - A*C - C

def heron (A C : ℚ) : ℚ := 2*A + 2*C + 2*A*C - A^2 - 1 - C^2

def sideA (s q : ℚ) : ℚ := 1 + q*(s^2-1)
def sideC (s q : ℚ) : ℚ := 1 + q*(2*s-1)
def alpha₁ (s : ℚ) : ℚ := (2*s^2-2*s-1)/3
def alpha₂ (s : ℚ) : ℚ := (-s^2+4*s-1)/3
def alpha₃ (s : ℚ) : ℚ := (-s^2-2*s+2)/3
def height (s : ℚ) : ℚ := 2*(s^2-s+1)/3
def coordinate (s q : ℚ) : ℚ := 1/q + (s^2+2*s-2)/3

lemma cone_parametrization (u v : ℚ) :
    IsSquare (u^2+v^2-u*v) ↔
      ∃ s q : ℚ, u = q*(s^2-1) ∧ v = q*(2*s-1) := by
  constructor
  · rintro ⟨e,he⟩
    by_cases hv : v = 0
    · refine ⟨1/2, -4*u/3, ?_, ?_⟩
      · ring
      · simp [hv]
    · let s := (e+u)/v
      have hs : s*v = e+u := by dsimp [s]; field_simp
      have he' : (s*v-u)^2 = u^2+v^2-u*v := by
        rw [show s*v-u = e by linarith]
        nlinarith [he]
      have hf : v*(v*(s^2-1)-u*(2*s-1)) = 0 := by nlinarith [he']
      have hr : v*(s^2-1)-u*(2*s-1) = 0 := (mul_eq_zero.mp hf).resolve_left hv
      have hd : 2*s-1 ≠ 0 := by
        intro hh
        have hh' : s = 1/2 := by linarith
        rw [hh'] at hr
        norm_num at hr
        apply hv
        linarith
      refine ⟨s, v/(2*s-1), ?_, ?_⟩
      · field_simp
        nlinarith [hr]
      · field_simp
  · rintro ⟨s,q,rfl,rfl⟩
    refine ⟨q*(s^2-s+1), ?_⟩
    ring

lemma delta_parametrization (A C : ℚ) :
    IsSquare (delta A C) ↔
      ∃ s q : ℚ, A = sideA s q ∧ C = sideC s q := by
  have he : delta A C = (A-1)^2+(C-1)^2-(A-1)*(C-1) := by unfold delta; ring
  rw [he, cone_parametrization]
  constructor
  · rintro ⟨s,q,hA,hC⟩
    exact ⟨s,q,by dsimp [sideA]; linarith,by dsimp [sideC]; linarith⟩
  · rintro ⟨s,q,hA,hC⟩
    exact ⟨s,q,by dsimp [sideA] at hA; linarith,by dsimp [sideC] at hC; linarith⟩

lemma delta_identity (s q : ℚ) :
    delta (sideA s q) (sideC s q) = (q*(s^2-s+1))^2 := by
  unfold delta sideA sideC
  ring

lemma heron_identity (s q : ℚ) :
    heron (sideA s q) (sideC s q) = (1+q*s^2)*(3-q*(s-2)^2) := by
  unfold heron sideA sideC
  ring

/-- The six square conditions, with positive (four times squared) area. -/
def Admissible (A C : ℚ) : Prop :=
  IsSquare A ∧ IsSquare C ∧
  IsSquare (2*A+2-C) ∧ IsSquare (2*A-1+2*C) ∧
  IsSquare (-A+2+2*C) ∧ IsSquare (delta A C) ∧ 0 < heron A C

/-- The remaining five square conditions after parametrizing the discriminant. -/
def ParamAdmissible (s q : ℚ) : Prop :=
  IsSquare (1+q*(s^2-1)) ∧ IsSquare (1+q*(2*s-1)) ∧
  IsSquare (3+q*(2*s^2-2*s-1)) ∧ IsSquare (3+2*q*(s^2+2*s-2)) ∧
  IsSquare (3+q*(-s^2+4*s-1)) ∧ 0 < (1+q*s^2)*(3-q*(s-2)^2)

lemma admissible_at_param (s q : ℚ) :
    Admissible (sideA s q) (sideC s q) ↔ ParamAdmissible s q := by
  have h₁ : 2*sideA s q+2-sideC s q = 3+q*(2*s^2-2*s-1) := by
    unfold sideA sideC; ring
  have h₂ : 2*sideA s q-1+2*sideC s q = 3+2*q*(s^2+2*s-2) := by
    unfold sideA sideC; ring
  have h₃ : -sideA s q+2+2*sideC s q = 3+q*(-s^2+4*s-1) := by
    unfold sideA sideC; ring
  have hd : IsSquare (delta (sideA s q) (sideC s q)) := by
    rw [delta_identity]
    exact IsSquare.sq _
  simp only [Admissible, h₁, h₂, h₃, hd, heron_identity, true_and]
  rfl

lemma admissible_parametrization (A C : ℚ) :
    Admissible A C ↔
      ∃ s q : ℚ, A = sideA s q ∧ C = sideC s q ∧ ParamAdmissible s q := by
  constructor
  · intro h
    obtain ⟨s,q,hA,hC⟩ := (delta_parametrization A C).mp h.2.2.2.2.2.1
    refine ⟨s,q,hA,hC,?_⟩
    rw [hA,hC] at h
    exact (admissible_at_param s q).mp h
  · rintro ⟨s,q,rfl,rfl,h⟩
    exact (admissible_at_param s q).mpr h

lemma alpha_sum (s : ℚ) : alpha₁ s + alpha₂ s + alpha₃ s = 0 := by
  unfold alpha₁ alpha₂ alpha₃
  ring

lemma alpha_squares (s : ℚ) :
    (alpha₁ s)^2+(alpha₂ s)^2+(alpha₃ s)^2 = 2*(s^2-s+1)^2/3 := by
  unfold alpha₁ alpha₂ alpha₃
  ring

lemma side_coordinates (s q : ℚ) (hq : q ≠ 0) :
    sideA s q = q*(coordinate s q+alpha₁ s) ∧
    sideC s q = q*(coordinate s q+alpha₂ s) ∧
    1 = q*(coordinate s q+alpha₃ s) := by
  unfold sideA sideC coordinate alpha₁ alpha₂ alpha₃
  constructor
  · field_simp; ring
  constructor <;> field_simp <;> ring

lemma median_coordinates (s q : ℚ) (hq : q ≠ 0) :
    -sideA s q+2+2*sideC s q = 3*q*(coordinate s q-alpha₁ s) ∧
    2*sideA s q+2-sideC s q = 3*q*(coordinate s q-alpha₂ s) ∧
    2*sideA s q-1+2*sideC s q = 3*q*(coordinate s q-alpha₃ s) := by
  unfold sideA sideC coordinate alpha₁ alpha₂ alpha₃
  constructor
  · field_simp; ring
  constructor <;> field_simp <;> ring

lemma heron_coordinate (s q : ℚ) (hq : q ≠ 0) :
    heron (sideA s q) (sideC s q) =
      3*q^2*((coordinate s q)^2-(height s)^2) := by
  unfold heron sideA sideC coordinate height
  field_simp
  ring

lemma positive_area_iff (s q : ℚ) (hq : q ≠ 0) :
    0 < heron (sideA s q) (sideC s q) ↔ (height s)^2 < (coordinate s q)^2 := by
  rw [heron_coordinate s q hq]
  have hp : 0 < 3*q^2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hq)
  rw [mul_pos_iff_of_pos_left hp, sub_pos]

lemma param_q_ne_zero {s q : ℚ} (h : ParamAdmissible s q) : q ≠ 0 := by
  rintro rfl
  have hh := h.2.2.1
  norm_num at hh

lemma heron_positive_sides {A C : ℚ} (hA : IsSquare A) (hC : IsSquare C)
    (hH : 0 < heron A C) : 0 < A ∧ 0 < C := by
  have hA0 : 0 ≤ A := hA.nonneg
  have hC0 : 0 ≤ C := hC.nonneg
  have hid : heron A C = 4*A*C-(A+C-1)^2 := by unfold heron; ring
  rw [hid] at hH
  constructor
  · by_contra h
    have hz : A = 0 := le_antisymm (le_of_not_gt h) hA0
    rw [hz] at hH
    nlinarith [sq_nonneg (C-1)]
  · by_contra h
    have hz : C = 0 := le_antisymm (le_of_not_gt h) hC0
    rw [hz] at hH
    nlinarith [sq_nonneg (A-1)]

lemma median_involution (s q : ℚ) (hd : 3+2*q*(s^2+2*s-2) ≠ 0) :
    let q' := -3*q/(3+2*q*(s^2+2*s-2))
    sideA s q' = (-sideA s q+2+2*sideC s q)/(2*sideA s q-1+2*sideC s q) ∧
    sideC s q' = (2*sideA s q+2-sideC s q)/(2*sideA s q-1+2*sideC s q) := by
  have hh : 2*sideA s q-1+2*sideC s q = 3+2*q*(s^2+2*s-2) := by
    unfold sideA sideC; ring
  dsimp only
  rw [hh]
  unfold sideA sideC
  have hv : (-3*q/(3+2*q*(s^2+2*s-2)))*(3+2*q*(s^2+2*s-2)) = -3*q :=
    div_mul_cancel₀ _ hd
  constructor
  · apply (eq_div_iff hd).mpr
    linear_combination (s^2-1)*hv
  · apply (eq_div_iff hd).mpr
    linear_combination (2*s-1)*hv


lemma coordinate_involution (s q : ℚ) (hq : q ≠ 0) :
    coordinate s (-3*q/(3+2*q*(s^2+2*s-2))) = -coordinate s q := by
  unfold coordinate
  field_simp
  ring

lemma root_difference_products (s q : ℚ) (hq : q ≠ 0) :
    sideA s q * (-sideA s q+2+2*sideC s q) =
      q^2*(3*((coordinate s q)^2-(alpha₁ s)^2)) ∧
    sideC s q * (2*sideA s q+2-sideC s q) =
      q^2*(3*((coordinate s q)^2-(alpha₂ s)^2)) ∧
    2*sideA s q-1+2*sideC s q =
      q^2*(3*((coordinate s q)^2-(alpha₃ s)^2)) := by
  obtain ⟨hA,hC,hB⟩ := side_coordinates s q hq
  obtain ⟨hM₃,hM₁,hM₂⟩ := median_coordinates s q hq
  constructor
  · rw [hM₃,hA]; ring
  constructor
  · rw [hM₁,hC]; ring
  · calc
      2*sideA s q-1+2*sideC s q = 1*(2*sideA s q-1+2*sideC s q) := by ring
      _ = (q*(coordinate s q+alpha₃ s))*(3*q*(coordinate s q-alpha₃ s)) := by
        rw [← hB,← hM₂]
      _ = _ := by ring

lemma root_difference_squares {s q : ℚ} (h : ParamAdmissible s q) :
    IsSquare (3*((coordinate s q)^2-(alpha₁ s)^2)) ∧
    IsSquare (3*((coordinate s q)^2-(alpha₂ s)^2)) ∧
    IsSquare (3*((coordinate s q)^2-(alpha₃ s)^2)) := by
  have hq := param_q_ne_zero h
  have ha := (admissible_at_param s q).mpr h
  obtain ⟨hp₁,hp₂,hp₃⟩ := root_difference_products s q hq
  have hq2 : IsSquare (q^2) := IsSquare.sq q
  have hcancel : ∀ u : ℚ, q^2*u/q^2 = u := fun u => by field_simp
  constructor
  · have hh := (ha.1.mul ha.2.2.2.2.1).div hq2
    rw [hp₁,hcancel] at hh
    exact hh
  constructor
  · have hh := (ha.2.1.mul ha.2.2.1).div hq2
    rw [hp₂,hcancel] at hh
    exact hh
  · have hh := ha.2.2.2.1.div hq2
    rw [hp₃,hcancel] at hh
    exact hh

/-- The necessary root-difference conditions, together with the two side
square conditions and positive area, are also sufficient. No elliptic
rational point by itself is asserted to be sufficient. -/
lemma admissible_iff_root_differences (s q : ℚ) (hq : q ≠ 0) :
    ParamAdmissible s q ↔
      IsSquare (sideA s q) ∧ IsSquare (sideC s q) ∧
      (height s)^2 < (coordinate s q)^2 ∧
      IsSquare (3*((coordinate s q)^2-(alpha₁ s)^2)) ∧
      IsSquare (3*((coordinate s q)^2-(alpha₂ s)^2)) ∧
      IsSquare (3*((coordinate s q)^2-(alpha₃ s)^2)) := by
  constructor
  · intro h
    have ha := (admissible_at_param s q).mpr h
    exact ⟨ha.1,ha.2.1,(positive_area_iff s q hq).mp ha.2.2.2.2.2.2,
      root_difference_squares h⟩
  · rintro ⟨hA,hC,hH,hd₁,hd₂,hd₃⟩
    apply (admissible_at_param s q).mp
    have hH' := (positive_area_iff s q hq).mpr hH
    obtain ⟨hA0,hC0⟩ := heron_positive_sides hA hC hH'
    obtain ⟨hp₁,hp₂,hp₃⟩ := root_difference_products s q hq
    have hq2 : IsSquare (q^2) := IsSquare.sq q
    have hM₁ : IsSquare (2*sideA s q+2-sideC s q) := by
      have hh := (hq2.mul hd₂).div hC
      rw [← hp₂,mul_div_cancel_left₀ _ (ne_of_gt hC0)] at hh
      exact hh
    have hM₃ : IsSquare (-sideA s q+2+2*sideC s q) := by
      have hh := (hq2.mul hd₁).div hA
      rw [← hp₁,mul_div_cancel_left₀ _ (ne_of_gt hA0)] at hh
      exact hh
    exact ⟨hA,hC,hM₁,hp₃ ▸ hq2.mul hd₃,hM₃,
      (delta_parametrization _ _).mpr ⟨s,q,rfl,rfl⟩,hH'⟩

lemma genus_two_necessary {s q : ℚ} (h : ParamAdmissible s q) :
    ∃ Y : ℚ, Y^2 = 3*((coordinate s q)^2-(alpha₁ s)^2)*
      ((coordinate s q)^2-(alpha₂ s)^2)*((coordinate s q)^2-(alpha₃ s)^2) := by
  obtain ⟨⟨r₁,hr₁⟩,⟨r₂,hr₂⟩,⟨r₃,hr₃⟩⟩ := root_difference_squares h
  refine ⟨r₁*r₂*r₃/3,?_⟩
  have he : r₁^2*r₂^2*r₃^2 =
      (3*((coordinate s q)^2-(alpha₁ s)^2))*
      (3*((coordinate s q)^2-(alpha₂ s)^2))*
      (3*((coordinate s q)^2-(alpha₃ s)^2)) := by
    simpa only [pow_two] using congrArg₂ (·*·) (congrArg₂ (·*·) hr₁ hr₂) hr₃ |>.symm
  nlinarith [he]

lemma negative_boundary (s : ℚ) (hs : s ≠ 0) :
    sideA s (-1/s^2) = (1/s)^2 ∧
    sideC s (-1/s^2) = ((s-1)/s)^2 ∧
    2*sideA s (-1/s^2)+2-sideC s (-1/s^2) = ((s+1)/s)^2 ∧
    2*sideA s (-1/s^2)-1+2*sideC s (-1/s^2) = ((s-2)/s)^2 ∧
    -sideA s (-1/s^2)+2+2*sideC s (-1/s^2) = ((2*s-1)/s)^2 ∧
    heron (sideA s (-1/s^2)) (sideC s (-1/s^2)) = 0 := by
  unfold sideA sideC heron
  repeat' constructor
  all_goals field_simp; ring

lemma positive_boundary (s : ℚ) (hs : s ≠ 2) :
    sideA s (3/(s-2)^2) = ((2*s-1)/(s-2))^2 ∧
    sideC s (3/(s-2)^2) = ((s+1)/(s-2))^2 ∧
    2*sideA s (3/(s-2)^2)+2-sideC s (3/(s-2)^2) = (3*(s-1)/(s-2))^2 ∧
    2*sideA s (3/(s-2)^2)-1+2*sideC s (3/(s-2)^2) = (3*s/(s-2))^2 ∧
    -sideA s (3/(s-2)^2)+2+2*sideC s (3/(s-2)^2) = (3/(s-2))^2 ∧
    heron (sideA s (3/(s-2)^2)) (sideC s (3/(s-2)^2)) = 0 := by
  have hd : s-2 ≠ 0 := sub_ne_zero.mpr hs
  unfold sideA sideC heron
  repeat' constructor
  all_goals field_simp [hd]; ring

lemma boundary_not_admissible (s : ℚ) :
    ¬ParamAdmissible s (-1/s^2) ∧ ¬ParamAdmissible s (3/(s-2)^2) := by
  constructor
  · intro h
    by_cases hs : s = 0
    · subst s
      exact param_q_ne_zero h (by norm_num)
    · have hh := (negative_boundary s hs).2.2.2.2.2
      have ha := (admissible_at_param s (-1/s^2)).mpr h
      have hp := ha.2.2.2.2.2.2
      rw [hh] at hp
      exact (lt_irrefl 0) hp
  · intro h
    by_cases hs : s = 2
    · subst s
      exact param_q_ne_zero h (by norm_num)
    · have hh := (positive_boundary s hs).2.2.2.2.2
      have ha := (admissible_at_param s (3/(s-2)^2)).mpr h
      have hp := ha.2.2.2.2.2.2
      rw [hh] at hp
      exact (lt_irrefl 0) hp

/-- The first elliptic quotient, in a monic Weierstrass model. -/
def EllipticOne (s x y : ℚ) : Prop :=
  y^2 = (x-3*(alpha₁ s)^2)*(x-3*(alpha₂ s)^2)*(x-3*(alpha₃ s)^2)

lemma elliptic_one_necessary {s q : ℚ} (h : ParamAdmissible s q) :
    ∃ y : ℚ, EllipticOne s (3*(coordinate s q)^2) y := by
  obtain ⟨Y,hY⟩ := genus_two_necessary h
  refine ⟨3*Y,?_⟩
  unfold EllipticOne
  linear_combination 9*hY

lemma boundary_point (s : ℚ) :
    EllipticOne s (4*(s^2-s+1)^2/3) ((2*s-1)*(1-s^2)*s*(s-2)) := by
  unfold EllipticOne alpha₁ alpha₂ alpha₃
  ring

lemma half_boundary_point (s : ℚ) :
    EllipticOne s ((s^2-s+1)^2/3) (-((2*s-1)*(1-s^2)*s*(s-2))) := by
  unfold EllipticOne alpha₁ alpha₂ alpha₃
  ring

lemma half_boundary_horizontal_tangent (s : ℚ) :
    let x := (s^2-s+1)^2/3
    (x-3*(alpha₂ s)^2)*(x-3*(alpha₃ s)^2) +
    (x-3*(alpha₁ s)^2)*(x-3*(alpha₃ s)^2) +
    (x-3*(alpha₁ s)^2)*(x-3*(alpha₂ s)^2) = 0 := by
  dsimp only
  unfold alpha₁ alpha₂ alpha₃
  ring

lemma alpha_height_gaps (s : ℚ) :
    3*((height s)^2-(alpha₁ s)^2) = (2*s-1)^2 ∧
    3*((height s)^2-(alpha₂ s)^2) = (s^2-1)^2 ∧
    3*((height s)^2-(alpha₃ s)^2) = (s*(s-2))^2 := by
  unfold height alpha₁ alpha₂ alpha₃
  constructor
  · ring
  constructor <;> ring

lemma height_positive (s : ℚ) : 0 < height s := by
  unfold height
  nlinarith [sq_nonneg (s-1/2)]

/-- All ten sections found by the quadratic-polynomial diagnostic are
outside the positive-area region. This lemma checks the sections, not
completeness of that diagnostic. -/
lemma small_sections_not_positive (s T : ℚ)
    (hT : T = alpha₁ s ∨ T = -alpha₁ s ∨
      T = alpha₂ s ∨ T = -alpha₂ s ∨
      T = alpha₃ s ∨ T = -alpha₃ s ∨
      T = height s ∨ T = -height s ∨
      T = height s/2 ∨ T = -height s/2) :
    ¬ (height s)^2 < T^2 := by
  obtain ⟨h₁,h₂,h₃⟩ := alpha_height_gaps s
  rcases hT with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals nlinarith [sq_nonneg (2*s-1),sq_nonneg (s^2-1),
    sq_nonneg (s*(s-2)),sq_nonneg (height s)]

lemma half_height_genus_two_point (s : ℚ) :
    (-((2*s-1)*(1-s^2)*s*(s-2))/3)^2 =
      3*((height s/2)^2-(alpha₁ s)^2)*
      ((height s/2)^2-(alpha₂ s)^2)*((height s/2)^2-(alpha₃ s)^2) := by
  unfold height alpha₁ alpha₂ alpha₃
  ring

lemma translated_root_differences_exclude_area (a b c T : ℚ)
    (hsum : a+b+c = 0) (hT : T^2 = a^2-3*b*c)
    (hb : IsSquare (3*(T^2-b^2))) (hc : IsSquare (3*(T^2-c^2))) :
    ¬ (2/3)*(a^2+b^2+c^2) < T^2 := by
  have ha : a = -b-c := by linarith
  have hsumdiff : 3*(T^2-b^2)+3*(T^2-c^2) = 3*(b-c)^2 := by
    rw [ha] at hT
    nlinarith [hT]
  have hbc : b = c := sub_eq_zero.mp (isSquare_pair_three_mul hb hc hsumdiff)
  intro harea
  rw [ha,hbc] at hT harea
  nlinarith [sq_nonneg c]

/-- No rational specialization of the three torsion-translated half-boundary
x-coordinates can satisfy the full arithmetic conditions. This concerns
these particular x-coordinates, not all points on the elliptic quotient. -/
lemma translated_sections_excluded {s q : ℚ} (h : ParamAdmissible s q) :
    (coordinate s q)^2 ≠ (alpha₁ s)^2-3*alpha₂ s*alpha₃ s ∧
    (coordinate s q)^2 ≠ (alpha₂ s)^2-3*alpha₁ s*alpha₃ s ∧
    (coordinate s q)^2 ≠ (alpha₃ s)^2-3*alpha₁ s*alpha₂ s := by
  obtain ⟨hd₁,hd₂,hd₃⟩ := root_difference_squares h
  have hp := ((admissible_iff_root_differences s q (param_q_ne_zero h)).mp h).2.2.1
  have he : (height s)^2 = (2/3)*((alpha₁ s)^2+(alpha₂ s)^2+(alpha₃ s)^2) := by
    unfold height alpha₁ alpha₂ alpha₃
    ring
  rw [he] at hp
  constructor
  · intro hT
    exact translated_root_differences_exclude_area _ _ _ _ (alpha_sum s) hT hd₂ hd₃ hp
  constructor
  · intro hT
    apply translated_root_differences_exclude_area (alpha₂ s) (alpha₁ s) (alpha₃ s)
      (coordinate s q) (by linarith [alpha_sum s]) hT hd₁ hd₃
    nlinarith [hp]
  · intro hT
    apply translated_root_differences_exclude_area (alpha₃ s) (alpha₁ s) (alpha₂ s)
      (coordinate s q) (by linarith [alpha_sum s]) hT hd₁ hd₂
    nlinarith [hp]

#print axioms cone_parametrization
#print axioms admissible_parametrization
#print axioms positive_area_iff
#print axioms admissible_iff_root_differences
#print axioms genus_two_necessary
#print axioms boundary_not_admissible
#print axioms elliptic_one_necessary
#print axioms small_sections_not_positive
#print axioms translated_sections_excluded
end Erdos213.MedianDiscriminant
