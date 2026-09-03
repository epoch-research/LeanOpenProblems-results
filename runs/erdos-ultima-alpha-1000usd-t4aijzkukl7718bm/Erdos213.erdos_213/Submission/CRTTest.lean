import Mathlib.Tactic

/-! Algebraic certificate for the constant-projection CRT calculation.
This file proves the explicit coefficient implication, not a theorem about
arbitrary rational-distance configurations. -/
namespace Erdos213.TorsionMetricCRT
set_option maxHeartbeats 2000000

def coeffs (r s : ℚ) : Fin 6 → Fin 5 → ℚ :=
  fun i j => match i.val, j.val with
    | 0, 0 => -15/8*r^2*s + 15/8*r^2
    | 0, 1 => 3/16*r^2*s - 3/16*r^2
    | 0, 2 => 3/16*r^2*s - 3/16*r^2
    | 0, 3 => 1/16*r^2*s - 1/16*r^2
    | 0, 4 => 1/16*r^2*s - 1/16*r^2
    | 1, 0 => -15/8*r*s^2 + 15/4*r*s - 15/8*r
    | 1, 1 => -3/16*r*s^2 + 3/8*r*s - 3/16*r
    | 1, 2 => 3/16*r*s^2 - 3/8*r*s + 3/16*r
    | 1, 3 => -1/16*r*s^2 + 1/8*r*s - 1/16*r
    | 1, 4 => 1/16*r*s^2 - 1/8*r*s + 1/16*r
    | 2, 0 => 13/8*r^2*s + 21/16*r*s^2 - 13/8*r^2 - 21/16*s^2 - 17/4*r + 17/4*s
    | 2, 1 => -1/8*r^2*s + 5/32*r*s^2 + 1/8*r^2 - 5/32*s^2 - 3/16*r + 3/16*s
    | 2, 2 => -3/16*r^2*s - 1/32*r*s^2 + 3/16*r^2 + 1/32*s^2 + 1/4*r - 1/4*s
    | 2, 3 => 1/32*r*s^2 - 1/32*s^2 - 1/16*r + 1/16*s
    | 2, 4 => -1/16*r^2*s - 1/32*r*s^2 + 1/16*r^2 + 1/32*s^2 + 1/8*r - 1/8*s
    | 3, 0 => 21/16*r^2*s + 13/8*r*s^2 - 47/8*r*s + 47/8*r - 47/16*s
    | 3, 1 => -5/32*r^2*s + 1/8*r*s^2 + 1/16*r*s - 1/16*r + 1/32*s
    | 3, 2 => -1/32*r^2*s - 3/16*r*s^2 + 7/16*r*s - 7/16*r + 7/32*s
    | 3, 3 => -1/32*r^2*s + 1/16*r*s - 1/16*r + 1/32*s
    | 3, 4 => -1/32*r^2*s - 1/16*r*s^2 + 3/16*r*s - 3/16*r + 3/32*s
    | 4, 0 => 17/16*r^2*s - 4*r^2 + 47/8*r*s + 17/4*s^2 - 115/16*s
    | 4, 1 => -3/32*r^2*s - 1/8*r^2 + 7/16*r*s - 1/16*s^2 - 5/32*s
    | 4, 2 => -1/32*r^2*s + 1/4*r^2 - 7/16*r*s - 1/4*s^2 + 15/32*s
    | 4, 3 => 1/32*r^2*s - 1/16*r*s + 1/16*s^2 - 1/32*s
    | 4, 4 => -1/32*r^2*s + 1/8*r^2 - 3/16*r*s - 1/8*s^2 + 7/32*s
    | 5, 0 => 17/16*r*s^2 - 17/4*r^2 - 8*r*s + 47/16*s^2 + 33/4*r
    | 5, 1 => 3/32*r*s^2 - 1/16*r^2 + 1/4*r*s - 7/32*s^2 - 1/16*r
    | 5, 2 => -1/32*r*s^2 + 1/4*r^2 + 1/2*r*s - 7/32*s^2 - 1/2*r
    | 5, 3 => -1/32*r*s^2 + 1/16*r^2 + 1/32*s^2 - 1/16*r
    | 5, 4 => -1/32*r*s^2 + 1/8*r^2 + 1/4*r*s - 3/32*s^2 - 1/4*r
    | _, _ => 0

def high (r s a b c d e : ℚ) (i : Fin 5) : ℚ :=
  coeffs r s 0 i+a*coeffs r s 1 i+b*coeffs r s 2 i+
    c*coeffs r s 3 i+d*coeffs r s 4 i+e*coeffs r s 5 i

private lemma case_0 (r s : ℚ)
    (h : ∀ i, high r s (-1) (-1) (-1) (-1) (-1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (-1/3*r^2*s - 2/9*r^2 + 7/3*r*s + 7/3*r - 8/3*s - 40/9) * h0 + (4*r - 8*s) * h1 + (-10/3*r^2*s + 4/9*r^2 + 70/3*r*s + 70/3*r - 80/3*s - 496/9) * h2 + (-8*r^2*s - 24*r^2 + 56*r*s + 20*r + 8*s - 32) * h3


#print axioms case_0
end Erdos213.TorsionMetricCRT
