import Mathlib

/-!
# An auxiliary finite-difference obstruction for unit-circle degenerations

This file does not prove `Erdos104.erdos_104` and does not import the problem specification.
It certifies a 13-stencil linear identity and the radical obstruction used with it.
The geometric degeneration and density arguments are not formalized here.
-/

namespace UnitCircleStress

/-- The second difference of a scalar array in an integral direction. -/
def second (a b x y : ℤ) (f : ℤ → ℤ → ℝ) : ℝ :=
  f (x + 2 * a) (y + 2 * b) - 2 * f (x + a) (y + b) + f x y

/-- Normal component of the second difference of a vector array. -/
def load (a b x y : ℤ) (f g : ℤ → ℤ → ℝ) : ℝ :=
  -(b : ℝ) * second a b x y f + (a : ℝ) * second a b x y g

/-- Exact cancellation on thirteen triples supported on eleven lattice points. -/
theorem thirteen_stencil_identity (f g : ℤ → ℤ → ℝ) :
    -load 1 0 0 0 f g - load 1 0 1 0 f g - 2 * load 1 0 1 1 f g
      - load 1 0 1 2 f g - load 1 0 2 2 f g
      + load 0 1 1 0 f g + load 0 1 2 0 f g + load 0 1 3 0 f g
      - load 1 1 0 0 f g - load 1 1 1 0 f g - load 1 1 2 0 f g
      + load 1 (-1) 1 2 f g + load 2 1 0 0 f g = 0 := by
  norm_num [load, second]
  ring

/-- First coordinate of the short polynomial syzygy. -/
theorem polynomial_syzygy_x (X Y : ℝ) :
    -(X + X^2 + X^3) * (Y - 1)^2
      - (-1 - X - X^2) * (X * Y - 1)^2
      + X * (X - Y)^2 - (X^2 * Y - 1)^2 = 0 := by
  ring

/-- Second coordinate of the short polynomial syzygy. -/
theorem polynomial_syzygy_y (X Y : ℝ) :
    (-1 - X - 2 * X * Y - X * Y^2 - X^2 * Y^2) * (X - 1)^2
      + (-1 - X - X^2) * (X * Y - 1)^2
      + X * (X - Y)^2 + 2 * (X^2 * Y - 1)^2 = 0 := by
  ring

/-- The three real numbers `1`, `sqrt 2`, `sqrt 5` have no relation with the
coefficient of `sqrt 5` normalized to one and the others rational. -/
theorem sqrt_five_ne_rat_add_rat_mul_sqrt_two (a b : ℚ) :
    Real.sqrt 5 ≠ (a : ℝ) + (b : ℝ) * Real.sqrt 2 := by
  intro h
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hi5 : Irrational (Real.sqrt 5) := by
    simpa using (show Nat.Prime 5 by norm_num).irrational_sqrt
  have hi10 : Irrational (Real.sqrt 10) := by
    norm_num [irrational_sqrt_ofNat_iff]
  by_cases hb : b = 0
  · subst b
    simp only [Rat.cast_zero, zero_mul, add_zero] at h
    exact hi5.ne_rat a h
  by_cases ha : a = 0
  · subst a
    have he : Real.sqrt 10 = ((2 * b : ℚ) : ℝ) := by
      calc
        Real.sqrt 10 = Real.sqrt 5 * Real.sqrt 2 := by
          rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)]
          norm_num
        _ = (b : ℝ) * (Real.sqrt 2 ^ 2) := by
          simp only [Rat.cast_zero, zero_add] at h
          rw [h]
          ring
        _ = ((2 * b : ℚ) : ℝ) := by rw [hs2]; push_cast; ring
    exact hi10.ne_rat (2 * b) he
  have hs : (5 : ℝ) = (a : ℝ)^2 + 2 * (b : ℝ)^2 +
      2 * (a : ℝ) * (b : ℝ) * Real.sqrt 2 := by
    calc
      (5 : ℝ) = Real.sqrt 5 ^ 2 := (Real.sq_sqrt (by norm_num)).symm
      _ = ((a : ℝ) + (b : ℝ) * Real.sqrt 2)^2 := by rw [h]
      _ = (a : ℝ)^2 + (b : ℝ)^2 * Real.sqrt 2 ^ 2 +
          2 * (a : ℝ) * (b : ℝ) * Real.sqrt 2 := by ring
      _ = _ := by rw [hs2]; ring
  apply irrational_sqrt_two.ne_rat ((5 - a^2 - 2 * b^2) / (2 * a * b))
  push_cast
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) ha') hb')).2
  nlinarith [hs]

/-- No rational linear combination with a nonzero coefficient on `sqrt 5` vanishes. -/
theorem rational_radical_combination_ne_zero (a b c : ℚ) (hc : c ≠ 0) :
    (a : ℝ) + (b : ℝ) * Real.sqrt 2 + (c : ℝ) * Real.sqrt 5 ≠ 0 := by
  intro h
  apply sqrt_five_ne_rat_add_rat_mul_sqrt_two (-a / c) (-b / c)
  push_cast
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  field_simp
  nlinarith [h]

/-- The rational (horizontal and vertical) part of the stencil stress. -/
def axisLoad (f g : ℤ → ℤ → ℝ) : ℝ :=
  -load 1 0 0 0 f g - load 1 0 1 0 f g - 2 * load 1 0 1 1 f g
    - load 1 0 1 2 f g - load 1 0 2 2 f g
    + load 0 1 1 0 f g + load 0 1 2 0 f g + load 0 1 3 0 f g

/-- The `sqrt 2` (diagonal) part of the stencil stress. -/
def diagonalLoad (f g : ℤ → ℤ → ℝ) : ℝ :=
  -load 1 1 0 0 f g - load 1 1 1 0 f g - load 1 1 2 0 f g
    + load 1 (-1) 1 2 f g

/-- Algebraic inconsistency of the three load classes. Unit-curvature signs
make the axis load rational, the diagonal load a rational multiple of `sqrt 2`,
and the last load a nonzero rational multiple of `sqrt 5`. -/
theorem no_three_load_classes (f g : ℤ → ℤ → ℝ) (a b c : ℚ) (hc : c ≠ 0)
    (hA : axisLoad f g = (a : ℝ))
    (hB : diagonalLoad f g = (b : ℝ) * Real.sqrt 2)
    (hC : load 2 1 0 0 f g = (c : ℝ) * Real.sqrt 5) : False := by
  have hid : axisLoad f g + diagonalLoad f g + load 2 1 0 0 f g = 0 := by
    dsimp [axisLoad, diagonalLoad]
    linarith [thirteen_stencil_identity f g]
  rw [hA, hB, hC] at hid
  exact rational_radical_combination_ne_zero a b c hc hid

end UnitCircleStress
