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

private lemma case_1 (r s : ℚ)
    (h : ∀ i, high r s (-1) (-1) (-1) (-1) (1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (-4/25*r^2*s^2 + 4/25*r^2*s + 4/25*r*s^2 - 4/25*r*s) * h0 + (2*r^2*s^2 - 2*r^2*s - 2*r*s^2 + 2*r*s) * h1 + (-68/25*r^2*s^2 + 68/25*r^2*s + 68/25*r*s^2 - 68/25*r*s) * h2 + (-14*r^2*s^2 + 14*r^2*s + 14*r*s^2 - 14*r*s) * h3

private lemma case_2 (r s : ℚ)
    (h : ∀ i, high r s (-1) (-1) (-1) (1) (-1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (-2*r^3 + 2*r^2*s + 2*r^2 - 2*r*s) * h0 + (4*r^3 - 4*r^2*s - 4*r^2 + 4*r*s) * h2 + (-72*r^3 + 72*r^2*s + 72*r^2 - 72*r*s) * h4

private lemma case_3 (r s : ℚ)
    (h : ∀ i, high r s (-1) (-1) (-1) (1) (1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (8/21*r^2*s^2 - 8/21*r^2*s - 8/21*r*s^2 + 8/21*r*s) * h0 + (-2*r^2*s^2 + 2*r^2*s + 2*r*s^2 - 2*r*s) * h1 + (136/21*r^2*s^2 - 136/21*r^2*s - 136/21*r*s^2 + 136/21*r*s) * h2 + (-2*r^2*s^2 + 2*r^2*s + 2*r*s^2 - 2*r*s) * h3

private lemma case_4 (r s : ℚ)
    (h : ∀ i, high r s (-1) (-1) (1) (-1) (-1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (r^2 - r) * h0 + (-2*r^2 + 2*r) * h1 + (4*r^3 - 4*r^2*s - 8*r^2 + 4*r*s + 4*r) * h2 + (8*r^3 - 8*r^2*s - 2*r^2 + 8*r*s - 6*r) * h3 + (-12*r^3 + 12*r^2*s + 54*r^2 - 12*r*s - 42*r) * h4

private lemma case_5 (r s : ℚ)
    (h : ∀ i, high r s (-1) (-1) (1) (-1) (1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (3/25*r^2*s - 3/25*r*s^2 - 3/25*r*s + 3/25*s^2) * h0 + (26/25*r^2*s - 26/25*r*s^2 - 26/25*r*s + 26/25*s^2) * h2

private lemma case_6 (r s : ℚ)
    (h : ∀ i, high r s (-1) (-1) (1) (1) (-1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (-5/24*r^2*s^3 - 19/8*r^2*s^2 - 5/24*s^4 + 19/8*r^2*s - 13/6*s^3 - 19/12*r^2 + 25/6*s^2) * h0 + (2*r^2*s^3 - 67/6*r^2*s^2 + 2*s^4 + 67/6*r^2*s - 79/6*s^3 - 43/6*r^2 + 49/3*s^2) * h1 + (-3/4*r^2*s^3 + 181/12*r^2*s^2 - 3/4*s^4 - 181/12*r^2*s + 95/6*s^3 + 31/3*r^2 - 74/3*s^2) * h2 + (-2*r^2*s^3 + 51/2*r^2*s^2 - 2*s^4 - 51/2*r^2*s + 55/2*s^3 + 43/2*r^2 - 45*s^2) * h3 + (-233/2*r^2*s^2 + 233/2*r^2*s - 233/2*s^3 - 157/2*r^2 + 195*s^2) * h4

private lemma case_7 (r s : ℚ)
    (h : ∀ i, high r s (-1) (-1) (1) (1) (1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (6*r*s - 3*s^2 - 6*r + 3*s) * h0 + (4*r*s - 2*s^2 - 4*r + 2*s) * h1 + (4*r*s^2 - 4*s^3 - 44*r*s + 28*s^2 + 40*r - 24*s) * h2 + (-8*r*s^2 + 8*s^3 + 28*r*s - 26*s^2 - 20*r + 18*s) * h3 + (-12*r*s^2 + 12*s^3 + 296*r*s - 166*s^2 - 284*r + 154*s) * h4

private lemma case_8 (r s : ℚ)
    (h : ∀ i, high r s (-1) (1) (-1) (-1) (-1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (9/37*r^2*s - 9/37*r*s + 7/37*s^2 - 6/37*r + 15/37*s - 16/37) * h0 + (56/37*r^2*s - 56/37*r*s + 60/37*s^2 + 12/37*r + 44/37*s - 116/37) * h1 + (190/37*r^2*s - 190/37*r*s + 82/37*s^2 - 28/37*r + 218/37*s - 272/37) * h2 + (-92/37*r^2*s + 92/37*r*s - 88/37*s^2 - 284/37*r + 192/37*s + 180/37) * h3

private lemma case_9 (r s : ℚ)
    (h : ∀ i, high r s (-1) (1) (-1) (-1) (1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (-1/25*r^2*s + 1/25*r*s^2 + 1/25*r^2 - 1/25*r*s) * h0 + (-42/25*r^2*s + 42/25*r*s^2 + 42/25*r^2 - 42/25*r*s) * h2

private lemma case_10 (r s : ℚ)
    (h : ∀ i, high r s (-1) (1) (-1) (1) (-1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (r^2*s - r*s^2 - r*s + s^2) * h2

private lemma case_11 (r s : ℚ)
    (h : ∀ i, high r s (-1) (1) (-1) (1) (1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (7/37*r^2*s + 2/37*r*s + 7/37*r) * h0 + (-60/37*r^2*s + 4/37*r*s - 60/37*r) * h1 + (82/37*r^2*s + 108/37*r*s + 82/37*r) * h2 + (88/37*r^2*s + 4/37*r*s + 88/37*r) * h3

private lemma case_12 (r s : ℚ)
    (h : ∀ i, high r s (-1) (1) (1) (-1) (-1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (8/21*r^2*s^2 - 8/21*r^2*s - 8/21*r*s^2 + 8/21*r*s) * h0 + (2*r^2*s^2 - 2*r^2*s - 2*r*s^2 + 2*r*s) * h1 + (136/21*r^2*s^2 - 136/21*r^2*s - 136/21*r*s^2 + 136/21*r*s) * h2 + (2*r^2*s^2 - 2*r^2*s - 2*r*s^2 + 2*r*s) * h3

private lemma case_13 (r s : ℚ)
    (h : ∀ i, high r s (-1) (1) (1) (-1) (1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (4/25*r*s^3 + 14/25*r^3 - 14/25*r*s^2 - 4/25*r*s) * h0 + (2*r*s^3 - 2*r*s) * h1 + (68/25*r*s^3 + 188/25*r^3 - 188/25*r*s^2 - 68/25*r*s) * h2 + (-14*r*s^3 + 14*r*s) * h3

private lemma case_14 (r s : ℚ)
    (h : ∀ i, high r s (-1) (1) (1) (1) (-1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (r^2*s^2 - r^2*s - r*s^2 + r*s) * h0 + (2*r^2*s^2 - 2*r^2*s - 2*r*s^2 + 2*r*s) * h1 + (4*r^2*s^2 - 4*r^2*s - 4*r*s^2 + 4*r*s) * h2 + (2*r^2*s^2 - 2*r^2*s - 2*r*s^2 + 2*r*s) * h3 + (26*r^2*s^2 - 26*r^2*s - 26*r*s^2 + 26*r*s) * h4

private lemma case_15 (r s : ℚ)
    (h : ∀ i, high r s (-1) (1) (1) (1) (1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (7/3*r*s^2 - 4/3*s^3 + 1/3*r*s - 2*s^2 - 34/9*s) * h0 + (-8*r*s + 4*s^2 + 4*s) * h1 + (70/3*r*s^2 - 40/3*s^3 + 10/3*r*s - 20*s^2 - 436/9*s) * h2 + (-56*r*s^2 + 32*s^3 + 64*r*s + 12*s^2 - 20*s) * h3

private lemma case_16 (r s : ℚ)
    (h : ∀ i, high r s (1) (-1) (-1) (-1) (-1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (-r*s + s) * h1 + (-8/7*r^2 + 8/7*r*s + 12/7*r - 8/7*s - 4/7) * h2 + (8*r^2 + r*s - 12*r - s + 4) * h3

private lemma case_17 (r s : ℚ)
    (h : ∀ i, high r s (1) (-1) (-1) (-1) (1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (r^2*s^2 - r^2*s - r*s^2 + r*s) * h0 + (2*r^2*s^2 - 2*r^2*s - 2*r*s^2 + 2*r*s) * h1 + (-12*r^2*s^2 + 12*r^2*s + 12*r*s^2 - 12*r*s) * h2 + (-14*r^2*s^2 + 14*r^2*s + 14*r*s^2 - 14*r*s) * h3 + (58*r^2*s^2 - 58*r^2*s - 58*r*s^2 + 58*r*s) * h4

private lemma case_18 (r s : ℚ)
    (h : ∀ i, high r s (1) (-1) (-1) (1) (-1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (-2*r^3 + 2*r^2*s + 2*r^2 - 2*r*s) * h0 + (4*r^3 - 4*r^2*s - 4*r^2 + 4*r*s) * h2 + (-72*r^3 + 72*r^2*s + 72*r^2 - 72*r*s) * h4

private lemma case_19 (r s : ℚ)
    (h : ∀ i, high r s (1) (-1) (-1) (1) (1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (8/7*r*s^5 + 2/7*r^3*s^2 - 2*r*s^4 - 4/7*r^3*s - 2/3*r*s^3 - 2/21*r^3 + 38/21*r*s^2 + 2/21*r*s) * h0 + (8*r*s^5 + 2*r^3*s^2 - 6*r*s^4 - 2*r^3*s - 8*r*s^3 + 4*r*s^2 + 2*r*s) * h1 + (80/7*r*s^5 + 20/7*r^3*s^2 - 20*r*s^4 - 40/7*r^3*s - 52/3*r*s^3 - 76/21*r^3 + 436/21*r*s^2 + 244/21*r*s) * h2 + (-24*r*s^5 - 6*r^3*s^2 + 82*r*s^4 + 22*r^3*s - 24*r*s^3 - 16*r^3 - 60*r*s^2 + 26*r*s) * h3

private lemma case_20 (r s : ℚ)
    (h : ∀ i, high r s (1) (-1) (1) (-1) (-1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (-7/25*r^2*s + 2/5*r*s - 7/25*r) * h0 + (2*r^2*s - 2*r*s + 2*r) * h1 + (-94/25*r^2*s + 24/5*r*s - 94/25*r) * h2 + (-2*r^2*s - 2*r*s - 2*r) * h3

private lemma case_21 (r s : ℚ)
    (h : ∀ i, high r s (1) (-1) (1) (-1) (1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (3/2*r^2*s - 3/2*r*s^2 - 3/2*r*s + 3/2*s^2) * h1 + (-r^2*s + r*s^2 + r*s - s^2) * h2 + (-3/2*r^2*s + 3/2*r*s^2 + 3/2*r*s - 3/2*s^2) * h3

private lemma case_22 (r s : ℚ)
    (h : ∀ i, high r s (1) (-1) (1) (1) (-1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (7/25*r^2*s - 7/25*r^2 + 7/25*s^2 + 1/25*r - 7/25*s + 7/25) * h0 + (36/25*r^2*s + 64/25*r^2 - 64/25*s^2 + 48/25*r - 36/25*s - 64/25) * h1 + (94/25*r^2*s - 94/25*r^2 + 94/25*s^2 + 42/25*r - 94/25*s + 94/25) * h2 + (-76/5*r^2*s - 24/5*r^2 + 24/5*s^2 - 48/5*r + 76/5*s + 24/5) * h3

private lemma case_23 (r s : ℚ)
    (h : ∀ i, high r s (1) (-1) (1) (1) (1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (2*r^3 - 2*r^2*s - 2*r^2 + 2*r*s) * h0 + (-8*r^3 + 8*r^2*s + 8*r^2 - 8*r*s) * h2 + (-8*r^3 + 8*r^2*s + 8*r^2 - 8*r*s) * h3 + (84*r^3 - 84*r^2*s - 84*r^2 + 84*r*s) * h4

private lemma case_24 (r s : ℚ)
    (h : ∀ i, high r s (1) (1) (-1) (-1) (-1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (-3/25*r^2*s + 7/25*s^2 - 3/25*r + 3/25*s - 4/25) * h0 + (2*s^2 - 2) * h1 + (-26/25*r^2*s + 94/25*s^2 - 26/25*r + 26/25*s - 68/25) * h2 + (-4*r^2*s - 2*s^2 - 4*r + 4*s + 6) * h3

private lemma case_25 (r s : ℚ)
    (h : ∀ i, high r s (1) (1) (-1) (-1) (1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (-7/25*r^2*s + 1/25*r*s - 1/25*s^2 - 1/25*r + 8/25*s) * h0 + (36/25*r^2*s - 48/25*r*s + 48/25*s^2 + 48/25*r - 84/25*s) * h1 + (-94/25*r^2*s + 42/25*r*s - 42/25*s^2 - 42/25*r + 136/25*s) * h2 + (-76/5*r^2*s + 48/5*r*s - 48/5*s^2 - 48/5*r + 124/5*s) * h3

private lemma case_26 (r s : ℚ)
    (h : ∀ i, high r s (1) (1) (-1) (1) (-1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (-2*r^2*s + 2*r*s^2 + 2*r*s - 2*s^2) * h2 + (6*r^2*s - 6*r*s^2 - 6*r*s + 6*s^2) * h4

private lemma case_27 (r s : ℚ)
    (h : ∀ i, high r s (1) (1) (-1) (1) (1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (-2*r*s^2 + 2*s^3 + 2*r*s - 2*s^2) * h0 + (8*r*s^2 - 8*s^3 - 8*r*s + 8*s^2) * h2 + (-8*r*s^2 + 8*s^3 + 8*r*s - 8*s^2) * h3 + (-84*r*s^2 + 84*s^3 + 84*r*s - 84*s^2) * h4

private lemma case_28 (r s : ℚ)
    (h : ∀ i, high r s (1) (1) (1) (-1) (-1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (2*r^2*s^2 - 2*r^2*s - 2*r*s^2 + 2*r*s) * h1 + (2*r^2*s^2 - 2*r^2*s - 2*r*s^2 + 2*r*s) * h3

private lemma case_29 (r s : ℚ)
    (h : ∀ i, high r s (1) (1) (1) (-1) (1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (-16/29*r^2*s^2 + 16/29*r^2*s - 16/29*s^3 - 22/29*r^2 + 38/29*s^2) * h0 + (84/29*r^2*s^2 - 84/29*r^2*s + 84/29*s^3 + 72/29*r^2 - 156/29*s^2) * h1 + (-272/29*r^2*s^2 + 272/29*r^2*s - 272/29*s^3 - 316/29*r^2 + 588/29*s^2) * h2 + (-20/29*r^2*s^2 + 20/29*r^2*s - 20/29*s^3 - 216/29*r^2 + 236/29*s^2) * h3

private lemma case_30 (r s : ℚ)
    (h : ∀ i, high r s (1) (1) (1) (1) (-1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (16/29*r^2*s^2 - 16/29*r^2*s - 16/29*r*s^2 + 16/29*r*s) * h0 + (84/29*r^2*s^2 - 84/29*r^2*s - 84/29*r*s^2 + 84/29*r*s) * h1 + (272/29*r^2*s^2 - 272/29*r^2*s - 272/29*r*s^2 + 272/29*r*s) * h2 + (-20/29*r^2*s^2 + 20/29*r^2*s + 20/29*r*s^2 - 20/29*r*s) * h3

private lemma case_31 (r s : ℚ)
    (h : ∀ i, high r s (1) (1) (1) (1) (1) i=0) : r*s*(r-1)*(s-1)*(s-r)=0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  dsimp [high, coeffs] at h0 h1 h2 h3 h4
  linear_combination (13/342*r^2*s^4 + 16/57*r^2*s^3 + 13/342*s^5 + 115/171*r^2*s^2 + 6/19*s^4 - 4/3*r^2*s + 347/342*s^3 - 200/171*r^2 + 49/342*s^2) * h0 + (-26/19*r^2*s^4 + 68/19*r^2*s^3 - 26/19*s^5 - 100/19*r^2*s^2 + 44/19*s^4 + 52/19*r^2*s - 94/19*s^3 + 64/19*r^2 + 18/19*s^2) * h1 + (221/171*r^2*s^4 - 80/57*r^2*s^3 + 221/171*s^5 + 2254/171*r^2*s^2 - 4/19*s^4 - 832/57*r^2*s + 2515/171*s^3 - 2912/171*r^2 + 473/171*s^2) * h2 + (-78/19*r^2*s^4 - 212/19*r^2*s^3 - 78/19*s^5 + 36*r^2*s^2 - 284/19*s^4 - 28/19*r^2*s + 318/19*s^3 - 192/19*r^2 - 130/19*s^2) * h3

def sign (b : Bool) : ℚ := if b then 1 else -1

lemma high_coefficients_force_boundary (r s : ℚ) (a b c d e : Bool)
    (h : ∀ i, high r s (sign a) (sign b) (sign c) (sign d) (sign e) i=0) :
    r*s*(r-1)*(s-1)*(s-r)=0 := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e
  · exact case_0 r s h
  · exact case_1 r s h
  · exact case_2 r s h
  · exact case_3 r s h
  · exact case_4 r s h
  · exact case_5 r s h
  · exact case_6 r s h
  · exact case_7 r s h
  · exact case_8 r s h
  · exact case_9 r s h
  · exact case_10 r s h
  · exact case_11 r s h
  · exact case_12 r s h
  · exact case_13 r s h
  · exact case_14 r s h
  · exact case_15 r s h
  · exact case_16 r s h
  · exact case_17 r s h
  · exact case_18 r s h
  · exact case_19 r s h
  · exact case_20 r s h
  · exact case_21 r s h
  · exact case_22 r s h
  · exact case_23 r s h
  · exact case_24 r s h
  · exact case_25 r s h
  · exact case_26 r s h
  · exact case_27 r s h
  · exact case_28 r s h
  · exact case_29 r s h
  · exact case_30 r s h
  · exact case_31 r s h

#print axioms high_coefficients_force_boundary
end Erdos213.TorsionMetricCRT
