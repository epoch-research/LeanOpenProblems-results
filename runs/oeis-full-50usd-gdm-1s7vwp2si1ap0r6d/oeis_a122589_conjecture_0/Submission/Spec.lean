import FormalConjectures.Util.ProblemImports

set_option linter.unusedSimpArgs false


open Int

/--
A122589: Expansion of $1/(1 - 11x + 45x^2 - 84x^3 + 70x^4 - 21x^5 + x^6)$.
The sequence is defined by the linear recurrence relation:
$a(n) = 11 a(n-1) - 45 a(n-2) + 84 a(n-3) - 70 a(n-4) + 21 a(n-5) - a(n-6)$ for $n \ge 6$.
The initial values are $a(0)=1, a(1)=11, a(2)=76, a(3)=425, a(4)=2109, a(5)=9709$.
-/
def a (n : ℕ) : ℕ :=
  let rec a_int : ℕ → ℤ := fun n =>
    match n with
    | 0 => 1
    | 1 => 11
    | 2 => 76
    | 3 => 425
    | 4 => 2109
    | 5 => 9709
    | k + 6 =>
      11 * a_int (k + 5)
      - 45 * a_int (k + 4)
      + 84 * a_int (k + 3)
      - 70 * a_int (k + 2)
      + 21 * a_int (k + 1)
      - a_int k
  (a_int n).toNat

open Polynomial

lemma cos_add_cos_sub (x y : ℝ) : Real.cos (x + y) + Real.cos (x - y) = 2 * Real.cos x * Real.cos y := by
  rw [Real.cos_add, Real.cos_sub]
  ring

lemma cos_prod (x y : ℝ) : Real.cos x * Real.cos y = (Real.cos (x + y) + Real.cos (x - y)) / 2 := by
  have := cos_add_cos_sub x y
  linarith

lemma cos_symm (k : ℝ) (a : ℝ) (h : a = Real.pi / 13) : Real.cos (k * a) = Real.cos ((26 - k) * a) := by
  have h26 : 26 * a = 2 * Real.pi := by
    rw [h]
    ring
  have : k * a = 2 * Real.pi - (26 - k) * a := by
    linarith
  rw [this, Real.cos_two_pi_sub]

lemma sin_pi_div_thirteen_ne_zero : Real.sin (Real.pi / 13) ≠ 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h0 : 0 < Real.pi / 13 := by linarith
  have h1 : Real.pi / 13 < Real.pi := by linarith
  have hpos : 0 < Real.sin (Real.pi / 13) := Real.sin_pos_of_pos_of_lt_pi h0 h1
  exact ne_of_gt hpos

lemma sin_mul_cos (x y : ℝ) : 2 * Real.sin x * Real.cos y = Real.sin (y + x) - Real.sin (y - x) := by
  rw [Real.sin_add, Real.sin_sub]
  ring

lemma sum_cos_six :
    Real.cos (2 * (Real.pi / 13)) +
    Real.cos (4 * (Real.pi / 13)) +
    Real.cos (6 * (Real.pi / 13)) +
    Real.cos (8 * (Real.pi / 13)) +
    Real.cos (10 * (Real.pi / 13)) +
    Real.cos (12 * (Real.pi / 13)) = -1 / 2 := by
  set a := Real.pi / 13
  have hsin : Real.sin a ≠ 0 := sin_pi_div_thirteen_ne_zero
  have h1 : 2 * Real.sin a * Real.cos (2 * a) = Real.sin (3 * a) - Real.sin a := by
    have := sin_mul_cos a (2 * a)
    have h_add : 2 * a + a = 3 * a := by ring
    have h_sub : 2 * a - a = a := by ring
    rw [h_add, h_sub] at this
    exact this
  have h2 : 2 * Real.sin a * Real.cos (4 * a) = Real.sin (5 * a) - Real.sin (3 * a) := by
    have := sin_mul_cos a (4 * a)
    have h_add : 4 * a + a = 5 * a := by ring
    have h_sub : 4 * a - a = 3 * a := by ring
    rw [h_add, h_sub] at this
    exact this
  have h3 : 2 * Real.sin a * Real.cos (6 * a) = Real.sin (7 * a) - Real.sin (5 * a) := by
    have := sin_mul_cos a (6 * a)
    have h_add : 6 * a + a = 7 * a := by ring
    have h_sub : 6 * a - a = 5 * a := by ring
    rw [h_add, h_sub] at this
    exact this
  have h4 : 2 * Real.sin a * Real.cos (8 * a) = Real.sin (9 * a) - Real.sin (7 * a) := by
    have := sin_mul_cos a (8 * a)
    have h_add : 8 * a + a = 9 * a := by ring
    have h_sub : 8 * a - a = 7 * a := by ring
    rw [h_add, h_sub] at this
    exact this
  have h5 : 2 * Real.sin a * Real.cos (10 * a) = Real.sin (11 * a) - Real.sin (9 * a) := by
    have := sin_mul_cos a (10 * a)
    have h_add : 10 * a + a = 11 * a := by ring
    have h_sub : 10 * a - a = 9 * a := by ring
    rw [h_add, h_sub] at this
    exact this
  have h6 : 2 * Real.sin a * Real.cos (12 * a) = Real.sin (13 * a) - Real.sin (11 * a) := by
    have := sin_mul_cos a (12 * a)
    have h_add : 12 * a + a = 13 * a := by ring
    have h_sub : 12 * a - a = 11 * a := by ring
    rw [h_add, h_sub] at this
    exact this
  have h13 : Real.sin (13 * a) = 0 := by
    have h_mul : 13 * a = Real.pi := by ring
    rw [h_mul, Real.sin_pi]
  have hmul : 2 * Real.sin a * (Real.cos (2 * a) + Real.cos (4 * a) + Real.cos (6 * a) + Real.cos (8 * a) + Real.cos (10 * a) + Real.cos (12 * a)) = - Real.sin a := by
    calc 2 * Real.sin a * (Real.cos (2 * a) + Real.cos (4 * a) + Real.cos (6 * a) + Real.cos (8 * a) + Real.cos (10 * a) + Real.cos (12 * a))
      _ = (2 * Real.sin a * Real.cos (2 * a)) + (2 * Real.sin a * Real.cos (4 * a)) + (2 * Real.sin a * Real.cos (6 * a)) + (2 * Real.sin a * Real.cos (8 * a)) + (2 * Real.sin a * Real.cos (10 * a)) + (2 * Real.sin a * Real.cos (12 * a)) := by ring
      _ = - Real.sin a := by linarith
  have hdiv : 2 * Real.sin a * (Real.cos (2 * a) + Real.cos (4 * a) + Real.cos (6 * a) + Real.cos (8 * a) + Real.cos (10 * a) + Real.cos (12 * a)) / (2 * Real.sin a) = - Real.sin a / (2 * Real.sin a) := by
    rw [hmul]
  have h_ne : 2 * Real.sin a ≠ 0 := mul_ne_zero (by norm_num) hsin
  rw [mul_div_cancel_left₀ _ h_ne] at hdiv
  have h_rhs : - Real.sin a / (2 * Real.sin a) = -1 / 2 := by
    calc - Real.sin a / (2 * Real.sin a)
      _ = (-1 / 2) * (Real.sin a / Real.sin a) := by ring
      _ = (-1 / 2) * 1 := by rw [div_self hsin]
      _ = -1 / 2 := by ring
  rw [h_rhs] at hdiv
  exact hdiv

lemma two_cos_sq (θ : ℝ) : 2 * Real.cos θ ^ 2 = Real.cos (2 * θ) + 1 := by
  have : Real.cos (2 * θ) = Real.cos (θ + θ) := by ring_nf
  rw [this, Real.cos_add]
  have hsin : Real.sin θ * Real.sin θ = Real.sin θ ^ 2 := by ring
  rw [hsin, Real.sin_sq]
  ring

lemma cos_sq (θ : ℝ) : Real.cos θ ^ 2 = (Real.cos (2 * θ) + 1) / 2 := by
  have := two_cos_sq θ
  linarith

lemma c_val (k : ℝ) : 4 * Real.cos (Real.pi * k / 13) ^ 2 = 2 * Real.cos (2 * k * Real.pi / 13) + 2 := by
  have : Real.pi * k / 13 = k * Real.pi / 13 := by ring
  rw [this]
  have h2 := two_cos_sq (k * Real.pi / 13)
  have h_arg : 2 * (k * Real.pi / 13) = 2 * k * Real.pi / 13 := by ring
  rw [h_arg] at h2
  linarith

lemma cos_twenty_six (a : ℝ) (h : a = Real.pi / 13) : Real.cos (26 * a) = 1 := by
  have h26 : 26 * a = 2 * Real.pi := by
    rw [h]
    ring
  rw [h26, Real.cos_two_pi]

lemma cos_add_twenty_six (k : ℝ) (a : ℝ) (h : a = Real.pi / 13) : Real.cos ((26 + k) * a) = Real.cos (k * a) := by
  have h26 : 26 * a = 2 * Real.pi := by
    rw [h]
    ring
  have : (26 + k) * a = 2 * Real.pi + k * a := by
    linarith
  rw [this, Real.cos_add, Real.cos_two_pi, Real.sin_two_pi]
  ring

set_option maxHeartbeats 2000000


/--
The conjecture suggested by the study of polynomials associated with the regular 13-gon
is that the denominator of the generating function for A122589 factors based on
the cosines of the angles of a regular 13-gon.
Specifically, let $P(x)$ be the denominator of the generating function. Then
$$P(x) = 1 - 11x + 45x^2 - 84x^3 + 70x^4 - 21x^5 + x^6 = \prod_{k=1}^6 \left(1 - 4 \cos^2\left(\frac{\pi k}{13}\right) x\right)$$
-/
theorem oeis_a122589_conjecture_0 :
    (C (1 : ℝ) - C (11 : ℝ) * X + C (45 : ℝ) * X^2 - C (84 : ℝ) * X^3 + C (70 : ℝ) * X^4 - C (21 : ℝ) * X^5 + C (1 : ℝ) * X^6)
    = Finset.prod (Finset.range 6)
        (fun k : ℕ => C (1 : ℝ) - C (4 * Real.cos (Real.pi * (k.succ : ℝ) / 13) ^ 2) * X) := by
  set c1 := 4 * Real.cos (Real.pi * 1 / 13) ^ 2
  set c2 := 4 * Real.cos (Real.pi * 2 / 13) ^ 2
  set c3 := 4 * Real.cos (Real.pi * 3 / 13) ^ 2
  set c4 := 4 * Real.cos (Real.pi * 4 / 13) ^ 2
  set c5 := 4 * Real.cos (Real.pi * 5 / 13) ^ 2
  set c6 := 4 * Real.cos (Real.pi * 6 / 13) ^ 2

  have h_unfold : Finset.prod (Finset.range 6) (fun k : ℕ => C (1 : ℝ) - C (4 * Real.cos (Real.pi * (k.succ : ℝ) / 13) ^ 2) * X) =
                  (C 1 - C c1 * X) * (C 1 - C c2 * X) * (C 1 - C c3 * X) * (C 1 - C c4 * X) * (C 1 - C c5 * X) * (C 1 - C c6 * X) := by
    simp only [c1, c2, c3, c4, c5, c6]
    simp [Finset.prod_range_succ]
    norm_num

  rw [h_unfold]

  have h_prod : (C 1 - C c1 * X) * (C 1 - C c2 * X) * (C 1 - C c3 * X) * (C 1 - C c4 * X) * (C 1 - C c5 * X) * (C 1 - C c6 * X) =
                C 1 - C (c1 + c2 + c3 + c4 + c5 + c6) * X +
                C (c1*c2 + c1*c3 + c1*c4 + c1*c5 + c1*c6 + c2*c3 + c2*c4 + c2*c5 + c2*c6 + c3*c4 + c3*c5 + c3*c6 + c4*c5 + c4*c6 + c5*c6) * X^2 -
                C (c1*c2*c3 + c1*c2*c4 + c1*c2*c5 + c1*c2*c6 + c1*c3*c4 + c1*c3*c5 + c1*c3*c6 + c1*c4*c5 + c1*c4*c6 + c1*c5*c6 +
                   c2*c3*c4 + c2*c3*c5 + c2*c3*c6 + c2*c4*c5 + c2*c4*c6 + c2*c5*c6 + c3*c4*c5 + c3*c4*c6 + c3*c5*c6 + c4*c5*c6) * X^3 +
                C (c1*c2*c3*c4 + c1*c2*c3*c5 + c1*c2*c3*c6 + c1*c2*c4*c5 + c1*c2*c4*c6 + c1*c2*c5*c6 + c1*c3*c4*c5 + c1*c3*c4*c6 +
                   c1*c3*c5*c6 + c1*c4*c5*c6 + c2*c3*c4*c5 + c2*c3*c4*c6 + c2*c3*c5*c6 + c2*c4*c5*c6 + c3*c4*c5*c6) * X^4 -
                C (c1*c2*c3*c4*c5 + c1*c2*c3*c4*c6 + c1*c2*c3*c5*c6 + c1*c2*c4*c5*c6 + c1*c3*c4*c5*c6 + c2*c3*c4*c5*c6) * X^5 +
                C (c1*c2*c3*c4*c5*c6) * X^6 := by
    simp only [map_add, map_mul, map_one]
    ring

  rw [h_prod]

  set a := Real.pi / 13
  have ha : a = Real.pi / 13 := rfl

  have cos_symm_14 : Real.cos (a * 14) = Real.cos (a * 12) := by
    have := cos_symm 14 a ha
    have h14 : 14 * a = a * 14 := by ring
    have h12 : (26 - 14) * a = a * 12 := by ring
    rw [h14, h12] at this; exact this
  have cos_symm_16 : Real.cos (a * 16) = Real.cos (a * 10) := by
    have := cos_symm 16 a ha
    have h16 : 16 * a = a * 16 := by ring
    have h10 : (26 - 16) * a = a * 10 := by ring
    rw [h16, h10] at this; exact this
  have cos_symm_18 : Real.cos (a * 18) = Real.cos (a * 8) := by
    have := cos_symm 18 a ha
    have h18 : 18 * a = a * 18 := by ring
    have h8 : (26 - 18) * a = a * 8 := by ring
    rw [h18, h8] at this; exact this
  have cos_symm_20 : Real.cos (a * 20) = Real.cos (a * 6) := by
    have := cos_symm 20 a ha
    have h20 : 20 * a = a * 20 := by ring
    have h6 : (26 - 20) * a = a * 6 := by ring
    rw [h20, h6] at this; exact this
  have cos_symm_22 : Real.cos (a * 22) = Real.cos (a * 4) := by
    have := cos_symm 22 a ha
    have h22 : 22 * a = a * 22 := by ring
    have h4 : (26 - 22) * a = a * 4 := by ring
    rw [h22, h4] at this; exact this
  have cos_symm_24 : Real.cos (a * 24) = Real.cos (a * 2) := by
    have := cos_symm 24 a ha
    have h24 : 24 * a = a * 24 := by ring
    have h2 : (26 - 24) * a = a * 2 := by ring
    rw [h24, h2] at this; exact this

  have cos_symm_26 : Real.cos (a * 26) = 1 := by
    have := cos_twenty_six a ha
    have h26 : 26 * a = a * 26 := by ring
    rw [h26] at this; exact this
  have cos_symm_28 : Real.cos (a * 28) = Real.cos (a * 2) := by
    have := cos_add_twenty_six 2 a ha
    have h28 : (26 + 2) * a = a * 28 := by ring
    have h2 : 2 * a = a * 2 := by ring
    rw [h28, h2] at this; exact this
  have cos_symm_30 : Real.cos (a * 30) = Real.cos (a * 4) := by
    have := cos_add_twenty_six 4 a ha
    have h30 : (26 + 4) * a = a * 30 := by ring
    have h4 : 4 * a = a * 4 := by ring
    rw [h30, h4] at this; exact this
  have cos_symm_32 : Real.cos (a * 32) = Real.cos (a * 6) := by
    have := cos_add_twenty_six 6 a ha
    have h32 : (26 + 6) * a = a * 32 := by ring
    have h6 : 6 * a = a * 6 := by ring
    rw [h32, h6] at this; exact this
  have cos_symm_34 : Real.cos (a * 34) = Real.cos (a * 8) := by
    have := cos_add_twenty_six 8 a ha
    have h34 : (26 + 8) * a = a * 34 := by ring
    have h8 : 8 * a = a * 8 := by ring
    rw [h34, h8] at this; exact this
  have cos_symm_36 : Real.cos (a * 36) = Real.cos (a * 10) := by
    have := cos_add_twenty_six 10 a ha
    have h36 : (26 + 10) * a = a * 36 := by ring
    have h10 : 10 * a = a * 10 := by ring
    rw [h36, h10] at this; exact this
  have cos_symm_38 : Real.cos (a * 38) = Real.cos (a * 12) := by
    have := cos_add_twenty_six 12 a ha
    have h38 : (26 + 12) * a = a * 38 := by ring
    have h12 : 12 * a = a * 12 := by ring
    rw [h38, h12] at this; exact this
  have cos_symm_40 : Real.cos (a * 40) = Real.cos (a * 12) := by
    have := cos_add_twenty_six 14 a ha
    have h40 : (26 + 14) * a = a * 40 := by ring
    have h14 : 14 * a = a * 14 := by ring
    rw [h40, h14] at this
    rw [this, cos_symm_14]
  have cos_symm_42 : Real.cos (a * 42) = Real.cos (a * 10) := by
    have := cos_add_twenty_six 16 a ha
    have h42 : (26 + 16) * a = a * 42 := by ring
    have h16 : 16 * a = a * 16 := by ring
    rw [h42, h16] at this
    rw [this, cos_symm_16]


  have h_sum : Real.cos (a * 2) + Real.cos (a * 4) + Real.cos (a * 6) + Real.cos (a * 8) + Real.cos (a * 10) + Real.cos (a * 12) = -1 / 2 := by
    have h2 : (Real.pi / 13) * 2 = 2 * (Real.pi / 13) := by ring
    have h4 : (Real.pi / 13) * 4 = 4 * (Real.pi / 13) := by ring
    have h6 : (Real.pi / 13) * 6 = 6 * (Real.pi / 13) := by ring
    have h8 : (Real.pi / 13) * 8 = 8 * (Real.pi / 13) := by ring
    have h10 : (Real.pi / 13) * 10 = 10 * (Real.pi / 13) := by ring
    have h12 : (Real.pi / 13) * 12 = 12 * (Real.pi / 13) := by ring
    rw [h2, h4, h6, h8, h10, h12]
    exact sum_cos_six

  have hc1 : c1 = 2 * Real.cos (2 * a) + 2 := by
    change 4 * Real.cos (Real.pi * 1 / 13) ^ 2 = 2 * Real.cos (2 * a) + 2
    have hval := c_val 1
    have h_arg : 2 * 1 * Real.pi / 13 = 2 * (Real.pi / 13) := by ring
    rw [h_arg] at hval; rw [← ha] at hval; exact hval
  have hc2 : c2 = 2 * Real.cos (4 * a) + 2 := by
    change 4 * Real.cos (Real.pi * 2 / 13) ^ 2 = 2 * Real.cos (4 * a) + 2
    have hval := c_val 2
    have h_arg : 2 * 2 * Real.pi / 13 = 4 * (Real.pi / 13) := by ring
    rw [h_arg] at hval; rw [← ha] at hval; exact hval
  have hc3 : c3 = 2 * Real.cos (6 * a) + 2 := by
    change 4 * Real.cos (Real.pi * 3 / 13) ^ 2 = 2 * Real.cos (6 * a) + 2
    have hval := c_val 3
    have h_arg : 2 * 3 * Real.pi / 13 = 6 * (Real.pi / 13) := by ring
    rw [h_arg] at hval; rw [← ha] at hval; exact hval
  have hc4 : c4 = 2 * Real.cos (8 * a) + 2 := by
    change 4 * Real.cos (Real.pi * 4 / 13) ^ 2 = 2 * Real.cos (8 * a) + 2
    have hval := c_val 4
    have h_arg : 2 * 4 * Real.pi / 13 = 8 * (Real.pi / 13) := by ring
    rw [h_arg] at hval; rw [← ha] at hval; exact hval
  have hc5 : c5 = 2 * Real.cos (10 * a) + 2 := by
    change 4 * Real.cos (Real.pi * 5 / 13) ^ 2 = 2 * Real.cos (10 * a) + 2
    have hval := c_val 5
    have h_arg : 2 * 5 * Real.pi / 13 = 10 * (Real.pi / 13) := by ring
    rw [h_arg] at hval; rw [← ha] at hval; exact hval
  have hc6 : c6 = 2 * Real.cos (12 * a) + 2 := by
    change 4 * Real.cos (Real.pi * 6 / 13) ^ 2 = 2 * Real.cos (12 * a) + 2
    have hval := c_val 6
    have h_arg : 2 * 6 * Real.pi / 13 = 12 * (Real.pi / 13) := by ring
    rw [h_arg] at hval; rw [← ha] at hval; exact hval

  have h_coeff1 : c1 + c2 + c3 + c4 + c5 + c6 = 11 := by
    rw [hc1, hc2, hc3, hc4, hc5, hc6]
    ring_nf
    linarith

  have h_E_1_1 : c1 = 2 + 2 * Real.cos (a * 2) := by
    rw [hc1]
    ring_nf

  have h_E_2_1_rec : c1 + c2 = (c1) + c2 := by ring
  have h_E_2_1 : c1 + c2 = 4 + 2 * Real.cos (a * 2) + 2 * Real.cos (a * 4) := by
    rw [h_E_2_1_rec]
    rw [h_E_1_1, hc2]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_2_2_rec : c1*c2 = (c1) * c2 := by ring
  have h_E_2_2 : c1*c2 = 4 + 6 * Real.cos (a * 2) + 4 * Real.cos (a * 4) + 2 * Real.cos (a * 6) := by
    rw [h_E_2_2_rec]
    rw [h_E_1_1, hc2]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_3_1_rec : c1 + c2 + c3 = (c1 + c2) + c3 := by ring
  have h_E_3_1 : c1 + c2 + c3 = 6 + 2 * Real.cos (a * 2) + 2 * Real.cos (a * 4) + 2 * Real.cos (a * 6) := by
    rw [h_E_3_1_rec]
    rw [h_E_2_1, hc3]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_3_2_rec : c1*c2 + c1*c3 + c2*c3 = (c1*c2) + (c1 + c2) * c3 := by ring
  have h_E_3_2 : c1*c2 + c1*c3 + c2*c3 = 12 + 12 * Real.cos (a * 2) + 10 * Real.cos (a * 4) + 10 * Real.cos (a * 6) + 2 * Real.cos (a * 8) + 2 * Real.cos (a * 10) := by
    rw [h_E_3_2_rec]
    rw [h_E_2_2, h_E_2_1, hc3]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_3_3_rec : c1*c2*c3 = (c1*c2) * c3 := by ring
  have h_E_3_3 : c1*c2*c3 = 10 + 16 * Real.cos (a * 2) + 14 * Real.cos (a * 4) + 12 * Real.cos (a * 6) + 6 * Real.cos (a * 8) + 4 * Real.cos (a * 10) + 2 * Real.cos (a * 12) := by
    rw [h_E_3_3_rec]
    rw [h_E_2_2, hc3]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_4_1_rec : c1 + c2 + c3 + c4 = (c1 + c2 + c3) + c4 := by ring
  have h_E_4_1 : c1 + c2 + c3 + c4 = 8 + 2 * Real.cos (a * 2) + 2 * Real.cos (a * 4) + 2 * Real.cos (a * 6) + 2 * Real.cos (a * 8) := by
    rw [h_E_4_1_rec]
    rw [h_E_3_1, hc4]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_4_2_rec : c1*c2 + c1*c3 + c1*c4 + c2*c3 + c2*c4 + c3*c4 = (c1*c2 + c1*c3 + c2*c3) + (c1 + c2 + c3) * c4 := by ring
  have h_E_4_2 : c1*c2 + c1*c3 + c1*c4 + c2*c3 + c2*c4 + c3*c4 = 24 + 18 * Real.cos (a * 2) + 16 * Real.cos (a * 4) + 16 * Real.cos (a * 6) + 14 * Real.cos (a * 8) + 4 * Real.cos (a * 10) + 4 * Real.cos (a * 12) := by
    rw [h_E_4_2_rec]
    rw [h_E_3_2, h_E_3_1, hc4]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_4_3_rec : c1*c2*c3 + c1*c2*c4 + c1*c3*c4 + c2*c3*c4 = (c1*c2*c3) + (c1*c2 + c1*c3 + c2*c3) * c4 := by ring
  have h_E_4_3 : c1*c2*c3 + c1*c2*c4 + c1*c3*c4 + c2*c3*c4 = 36 + 52 * Real.cos (a * 2) + 44 * Real.cos (a * 4) + 44 * Real.cos (a * 6) + 36 * Real.cos (a * 8) + 22 * Real.cos (a * 10) + 22 * Real.cos (a * 12) := by
    rw [h_E_4_3_rec]
    rw [h_E_3_3, h_E_3_2, hc4]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_4_4_rec : c1*c2*c3*c4 = (c1*c2*c3) * c4 := by ring
  have h_E_4_4 : c1*c2*c3*c4 = 26 + 48 * Real.cos (a * 2) + 44 * Real.cos (a * 4) + 42 * Real.cos (a * 6) + 36 * Real.cos (a * 8) + 30 * Real.cos (a * 10) + 30 * Real.cos (a * 12) := by
    rw [h_E_4_4_rec]
    rw [h_E_3_3, hc4]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_5_1_rec : c1 + c2 + c3 + c4 + c5 = (c1 + c2 + c3 + c4) + c5 := by ring
  have h_E_5_1 : c1 + c2 + c3 + c4 + c5 = 10 + 2 * Real.cos (a * 2) + 2 * Real.cos (a * 4) + 2 * Real.cos (a * 6) + 2 * Real.cos (a * 8) + 2 * Real.cos (a * 10) := by
    rw [h_E_5_1_rec]
    rw [h_E_4_1, hc5]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_5_2_rec : c1*c2 + c1*c3 + c1*c4 + c1*c5 + c2*c3 + c2*c4 + c2*c5 + c3*c4 + c3*c5 + c4*c5 = (c1*c2 + c1*c3 + c1*c4 + c2*c3 + c2*c4 + c3*c4) + (c1 + c2 + c3 + c4) * c5 := by ring
  have h_E_5_2 : c1*c2 + c1*c3 + c1*c4 + c1*c5 + c2*c3 + c2*c4 + c2*c5 + c3*c4 + c3*c5 + c4*c5 = 40 + 24 * Real.cos (a * 2) + 22 * Real.cos (a * 4) + 22 * Real.cos (a * 6) + 22 * Real.cos (a * 8) + 22 * Real.cos (a * 10) + 8 * Real.cos (a * 12) := by
    rw [h_E_5_2_rec]
    rw [h_E_4_2, h_E_4_1, hc5]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_5_3_rec : c1*c2*c3 + c1*c2*c4 + c1*c2*c5 + c1*c3*c4 + c1*c3*c5 + c1*c4*c5 + c2*c3*c4 + c2*c3*c5 + c2*c4*c5 + c3*c4*c5 = (c1*c2*c3 + c1*c2*c4 + c1*c3*c4 + c2*c3*c4) + (c1*c2 + c1*c3 + c1*c4 + c2*c3 + c2*c4 + c3*c4) * c5 := by ring
  have h_E_5_3 : c1*c2*c3 + c1*c2*c4 + c1*c2*c5 + c1*c3*c4 + c1*c3*c5 + c1*c4*c5 + c2*c3*c4 + c2*c3*c5 + c2*c4*c5 + c3*c4*c5 = 88 + 106 * Real.cos (a * 2) + 96 * Real.cos (a * 4) + 96 * Real.cos (a * 6) + 96 * Real.cos (a * 8) + 94 * Real.cos (a * 10) + 64 * Real.cos (a * 12) := by
    rw [h_E_5_3_rec]
    rw [h_E_4_3, h_E_4_2, hc5]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_5_4_rec : c1*c2*c3*c4 + c1*c2*c3*c5 + c1*c2*c4*c5 + c1*c3*c4*c5 + c2*c3*c4*c5 = (c1*c2*c3*c4) + (c1*c2*c3 + c1*c2*c4 + c1*c3*c4 + c2*c3*c4) * c5 := by ring
  have h_E_5_4 : c1*c2*c3*c4 + c1*c2*c3*c5 + c1*c2*c4*c5 + c1*c3*c4*c5 + c2*c3*c4*c5 = 120 + 210 * Real.cos (a * 2) + 198 * Real.cos (a * 4) + 196 * Real.cos (a * 6) + 196 * Real.cos (a * 8) + 190 * Real.cos (a * 10) + 170 * Real.cos (a * 12) := by
    rw [h_E_5_4_rec]
    rw [h_E_4_4, h_E_4_3, hc5]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_5_5_rec : c1*c2*c3*c4*c5 = (c1*c2*c3*c4) * c5 := by ring
  have h_E_5_5 : c1*c2*c3*c4*c5 = 82 + 162 * Real.cos (a * 2) + 160 * Real.cos (a * 4) + 158 * Real.cos (a * 6) + 156 * Real.cos (a * 8) + 154 * Real.cos (a * 10) + 152 * Real.cos (a * 12) := by
    rw [h_E_5_5_rec]
    rw [h_E_4_4, hc5]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_6_1_rec : c1 + c2 + c3 + c4 + c5 + c6 = (c1 + c2 + c3 + c4 + c5) + c6 := by ring
  have h_E_6_1 : c1 + c2 + c3 + c4 + c5 + c6 = 12 + 2 * Real.cos (a * 2) + 2 * Real.cos (a * 4) + 2 * Real.cos (a * 6) + 2 * Real.cos (a * 8) + 2 * Real.cos (a * 10) + 2 * Real.cos (a * 12) := by
    rw [h_E_6_1_rec]
    rw [h_E_5_1, hc6]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_6_2_rec : c1*c2 + c1*c3 + c1*c4 + c1*c5 + c1*c6 + c2*c3 + c2*c4 + c2*c5 + c2*c6 + c3*c4 + c3*c5 + c3*c6 + c4*c5 + c4*c6 + c5*c6 = (c1*c2 + c1*c3 + c1*c4 + c1*c5 + c2*c3 + c2*c4 + c2*c5 + c3*c4 + c3*c5 + c4*c5) + (c1 + c2 + c3 + c4 + c5) * c6 := by ring
  have h_E_6_2 : c1*c2 + c1*c3 + c1*c4 + c1*c5 + c1*c6 + c2*c3 + c2*c4 + c2*c5 + c2*c6 + c3*c4 + c3*c5 + c3*c6 + c4*c5 + c4*c6 + c5*c6 = 60 + 30 * Real.cos (a * 2) + 30 * Real.cos (a * 4) + 30 * Real.cos (a * 6) + 30 * Real.cos (a * 8) + 30 * Real.cos (a * 10) + 30 * Real.cos (a * 12) := by
    rw [h_E_6_2_rec]
    rw [h_E_5_2, h_E_5_1, hc6]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_6_3_rec : c1*c2*c3 + c1*c2*c4 + c1*c2*c5 + c1*c2*c6 + c1*c3*c4 + c1*c3*c5 + c1*c3*c6 + c1*c4*c5 + c1*c4*c6 + c1*c5*c6 + c2*c3*c4 + c2*c3*c5 + c2*c3*c6 + c2*c4*c5 + c2*c4*c6 + c2*c5*c6 + c3*c4*c5 + c3*c4*c6 + c3*c5*c6 + c4*c5*c6 = (c1*c2*c3 + c1*c2*c4 + c1*c2*c5 + c1*c3*c4 + c1*c3*c5 + c1*c4*c5 + c2*c3*c4 + c2*c3*c5 + c2*c4*c5 + c3*c4*c5) + (c1*c2 + c1*c3 + c1*c4 + c1*c5 + c2*c3 + c2*c4 + c2*c5 + c3*c4 + c3*c5 + c4*c5) * c6 := by ring
  have h_E_6_3 : c1*c2*c3 + c1*c2*c4 + c1*c2*c5 + c1*c2*c6 + c1*c3*c4 + c1*c3*c5 + c1*c3*c6 + c1*c4*c5 + c1*c4*c6 + c1*c5*c6 + c2*c3*c4 + c2*c3*c5 + c2*c3*c6 + c2*c4*c5 + c2*c4*c6 + c2*c5*c6 + c3*c4*c5 + c3*c4*c6 + c3*c5*c6 + c4*c5*c6 = 176 + 184 * Real.cos (a * 2) + 184 * Real.cos (a * 4) + 184 * Real.cos (a * 6) + 184 * Real.cos (a * 8) + 184 * Real.cos (a * 10) + 184 * Real.cos (a * 12) := by
    rw [h_E_6_3_rec]
    rw [h_E_5_3, h_E_5_2, hc6]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_6_4_rec : c1*c2*c3*c4 + c1*c2*c3*c5 + c1*c2*c3*c6 + c1*c2*c4*c5 + c1*c2*c4*c6 + c1*c2*c5*c6 + c1*c3*c4*c5 + c1*c3*c4*c6 + c1*c3*c5*c6 + c1*c4*c5*c6 + c2*c3*c4*c5 + c2*c3*c4*c6 + c2*c3*c5*c6 + c2*c4*c5*c6 + c3*c4*c5*c6 = (c1*c2*c3*c4 + c1*c2*c3*c5 + c1*c2*c4*c5 + c1*c3*c4*c5 + c2*c3*c4*c5) + (c1*c2*c3 + c1*c2*c4 + c1*c2*c5 + c1*c3*c4 + c1*c3*c5 + c1*c4*c5 + c2*c3*c4 + c2*c3*c5 + c2*c4*c5 + c3*c4*c5) * c6 := by ring
  have h_E_6_4 : c1*c2*c3*c4 + c1*c2*c3*c5 + c1*c2*c3*c6 + c1*c2*c4*c5 + c1*c2*c4*c6 + c1*c2*c5*c6 + c1*c3*c4*c5 + c1*c3*c4*c6 + c1*c3*c5*c6 + c1*c4*c5*c6 + c2*c3*c4*c5 + c2*c3*c4*c6 + c2*c3*c5*c6 + c2*c4*c5*c6 + c3*c4*c5*c6 = 360 + 580 * Real.cos (a * 2) + 580 * Real.cos (a * 4) + 580 * Real.cos (a * 6) + 580 * Real.cos (a * 8) + 580 * Real.cos (a * 10) + 580 * Real.cos (a * 12) := by
    rw [h_E_6_4_rec]
    rw [h_E_5_4, h_E_5_3, hc6]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_6_5_rec : c1*c2*c3*c4*c5 + c1*c2*c3*c4*c6 + c1*c2*c3*c5*c6 + c1*c2*c4*c5*c6 + c1*c3*c4*c5*c6 + c2*c3*c4*c5*c6 = (c1*c2*c3*c4*c5) + (c1*c2*c3*c4 + c1*c2*c3*c5 + c1*c2*c4*c5 + c1*c3*c4*c5 + c2*c3*c4*c5) * c6 := by ring
  have h_E_6_5 : c1*c2*c3*c4*c5 + c1*c2*c3*c4*c6 + c1*c2*c3*c5*c6 + c1*c2*c4*c5*c6 + c1*c3*c4*c5*c6 + c2*c3*c4*c5*c6 = 492 + 942 * Real.cos (a * 2) + 942 * Real.cos (a * 4) + 942 * Real.cos (a * 6) + 942 * Real.cos (a * 8) + 942 * Real.cos (a * 10) + 942 * Real.cos (a * 12) := by
    rw [h_E_6_5_rec]
    rw [h_E_5_5, h_E_5_4, hc6]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_E_6_6_rec : c1*c2*c3*c4*c5*c6 = (c1*c2*c3*c4*c5) * c6 := by ring
  have h_E_6_6 : c1*c2*c3*c4*c5*c6 = 316 + 630 * Real.cos (a * 2) + 630 * Real.cos (a * 4) + 630 * Real.cos (a * 6) + 630 * Real.cos (a * 8) + 630 * Real.cos (a * 10) + 630 * Real.cos (a * 12) := by
    rw [h_E_6_6_rec]
    rw [h_E_5_5, hc6]
    ring_nf
    try simp only [cos_prod, cos_sq]
    try ring_nf
    try simp only [Real.cos_zero, Real.cos_neg, cos_symm_14, cos_symm_16, cos_symm_18, cos_symm_20, cos_symm_22, cos_symm_24, cos_symm_26, cos_symm_28, cos_symm_30, cos_symm_32, cos_symm_34, cos_symm_36, cos_symm_38, cos_symm_40, cos_symm_42]
    try ring_nf

  have h_coeff2 : c1*c2 + c1*c3 + c1*c4 + c1*c5 + c1*c6 + c2*c3 + c2*c4 + c2*c5 + c2*c6 + c3*c4 + c3*c5 + c3*c6 + c4*c5 + c4*c6 + c5*c6 = 45 := by
    rw [h_E_6_2]
    linarith [h_sum]

  have h_coeff3 : c1*c2*c3 + c1*c2*c4 + c1*c2*c5 + c1*c2*c6 + c1*c3*c4 + c1*c3*c5 + c1*c3*c6 + c1*c4*c5 + c1*c4*c6 + c1*c5*c6 +
                  c2*c3*c4 + c2*c3*c5 + c2*c3*c6 + c2*c4*c5 + c2*c4*c6 + c2*c5*c6 + c3*c4*c5 + c3*c4*c6 + c3*c5*c6 + c4*c5*c6 = 84 := by
    rw [h_E_6_3]
    linarith [h_sum]

  have h_coeff4 : c1*c2*c3*c4 + c1*c2*c3*c5 + c1*c2*c3*c6 + c1*c2*c4*c5 + c1*c2*c4*c6 + c1*c2*c5*c6 + c1*c3*c4*c5 + c1*c3*c4*c6 +
                  c1*c3*c5*c6 + c1*c4*c5*c6 + c2*c3*c4*c5 + c2*c3*c4*c6 + c2*c3*c5*c6 + c2*c4*c5*c6 + c3*c4*c5*c6 = 70 := by
    rw [h_E_6_4]
    linarith [h_sum]

  have h_coeff5 : c1*c2*c3*c4*c5 + c1*c2*c3*c4*c6 + c1*c2*c3*c5*c6 + c1*c2*c4*c5*c6 + c1*c3*c4*c5*c6 + c2*c3*c4*c5*c6 = 21 := by
    rw [h_E_6_5]
    linarith [h_sum]

  have h_coeff6 : c1*c2*c3*c4*c5*c6 = 1 := by
    rw [h_E_6_6]
    linarith [h_sum]

  rw [h_coeff1, h_coeff2, h_coeff3, h_coeff4, h_coeff5, h_coeff6]

instance : Coe ℕ ℝ where
  coe := Nat.cast






