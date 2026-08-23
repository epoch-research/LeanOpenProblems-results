import FormalConjectures.Util.ProblemImports

open Nat Int

/--
A113254: Corresponds to $m = 8$ in a family of 4th-order linear recurrence sequences.

The sequence $a(n)$ is defined by the initial conditions $a(0)=-1, a(1)=4, a(2)=176, a(3)=3136$,
and the linear recurrence relation $a(n) = -4 * a (n-1) + 256 * a (n-3) + 4096 * a (n-4)$ for $n \ge 4$.
-/
def a (n : ℕ) : ℤ :=
  match n with
  | 0 => -1
  | 1 => 4
  | 2 => 176
  | 3 => 3136
  | n' + 4 => -4 * a (n' + 3) + 256 * a (n' + 1) + 4096 * a n'

/-- Companion Lucas sequence `V_n(-2, 16)`. -/
def v : ℕ → ℤ
  | 0 => 2
  | 1 => -2
  | n + 2 => -2 * v (n + 1) - 16 * v n

lemma a_zero : a 0 = -1 := rfl
lemma a_one : a 1 = 4 := rfl
lemma a_two : a 2 = 176 := rfl
lemma a_three : a 3 = 3136 := rfl

lemma a_add_four (n : ℕ) :
    a (n + 4) = -4 * a (n + 3) + 256 * a (n + 1) + 4096 * a n :=
  rfl

lemma v_zero : v 0 = 2 := rfl
lemma v_one : v 1 = -2 := rfl

lemma v_add_two (n : ℕ) : v (n + 2) = -2 * v (n + 1) - 16 * v n :=
  rfl

lemma v_succ_succ (n : ℕ) : v (n + 2) + 2 * v (n + 1) + 16 * v n = 0 := by
  rw [v_add_two]; ring

/-- The pair `(x n, y n)` represents `(-1 + √(-15))^n`. -/
def xy : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    let x := (xy n).1
    let y := (xy n).2
    (-x - 15 * y, x - y)

def x (n : ℕ) : ℤ := (xy n).1
def y (n : ℕ) : ℤ := (xy n).2

lemma x_zero : x 0 = 1 := rfl
lemma y_zero : y 0 = 0 := rfl

lemma x_succ (n : ℕ) : x (n + 1) = -x n - 15 * y n := rfl
lemma y_succ (n : ℕ) : y (n + 1) = x n - y n := rfl

lemma x_sq_add_fifteen_y_sq (n : ℕ) : x n ^ 2 + 15 * y n ^ 2 = 16 ^ n := by
  induction n with
  | zero =>
    simp [x_zero, y_zero]
  | succ n ih =>
    rw [x_succ, y_succ, pow_succ]
    linear_combination 16 * ih

lemma xy_add (m n : ℕ) :
    x (m + n) = x m * x n - 15 * y m * y n ∧
    y (m + n) = x m * y n + y m * x n := by
  induction n generalizing m with
  | zero =>
    simp [x_zero, y_zero]
  | succ n ih =>
    obtain ⟨ihx, ihy⟩ := ih m
    constructor
    · rw [add_succ, x_succ, ihx, ihy, x_succ, y_succ]
      ring
    · rw [add_succ, y_succ, ihx, ihy, x_succ, y_succ]
      ring

lemma x_add (m n : ℕ) :
    x (m + n) = x m * x n - 15 * y m * y n :=
  (xy_add m n).1

lemma y_add (m n : ℕ) :
    y (m + n) = x m * y n + y m * x n :=
  (xy_add m n).2

lemma x_two_mul (n : ℕ) : x (2 * n) = x n ^ 2 - 15 * y n ^ 2 := by
  rw [two_mul, x_add]
  ring

lemma v_eq_two_x : ∀ n, v n = 2 * x n
  | 0 => by simp [v_zero, x_zero]
  | 1 => by simp [v_one, x_succ, x_zero, y_zero]
  | n + 2 => by
    rw [v_add_two, v_eq_two_x (n + 1), v_eq_two_x n]
    rw [x_succ (n + 1), y_succ n, x_succ n]
    ring

lemma v_sq (n : ℕ) : v n ^ 2 = v (2 * n) + 2 * 16 ^ n := by
  simp only [v_eq_two_x, x_two_mul]
  have hnorm := x_sq_add_fifteen_y_sq n
  linear_combination 2 * hnorm

/-- Closed form auxiliary: `P n = 2 * a n`. -/
def P (n : ℕ) : ℤ :=
  (2 : ℤ) ^ n * v (n + 1) + (2 : ℤ) ^ (3 * n + 2) * (1 - (-1 : ℤ) ^ n)

lemma P_eq_geom (n : ℕ) :
    P n = (2 : ℤ) ^ n * v (n + 1) + 4 * ((8 : ℤ) ^ n - (-8 : ℤ) ^ n) := by
  simp only [P]
  have hpow : (2 : ℤ) ^ (3 * n + 2) = 4 * (8 : ℤ) ^ n := by
    rw [pow_add, pow_mul, show (2 : ℤ) ^ 3 = 8 by norm_num]
    ring
  rw [hpow]
  have hsplit : (4 : ℤ) * ((8 : ℤ) ^ n - (-8 : ℤ) ^ n) =
      4 * (8 : ℤ) ^ n * (1 - (-1 : ℤ) ^ n) := by
    have : (-8 : ℤ) ^ n = (-1 : ℤ) ^ n * (8 : ℤ) ^ n := by
      rw [show (-8 : ℤ) = (-1) * 8 by norm_num, mul_pow]
    rw [this]
    ring
  rw [← hsplit]

lemma eight_pow_rec (n : ℕ) :
    (8 : ℤ) ^ (n + 4) + 4 * (8 : ℤ) ^ (n + 3) - 256 * (8 : ℤ) ^ (n + 1) -
      4096 * (8 : ℤ) ^ n = 0 := by
  have h4 : (8 : ℤ) ^ (n + 4) = 4096 * (8 : ℤ) ^ n := by
    rw [pow_add]; norm_num; ring
  have h3 : (8 : ℤ) ^ (n + 3) = 512 * (8 : ℤ) ^ n := by
    rw [pow_add]; norm_num; ring
  have h1 : (8 : ℤ) ^ (n + 1) = 8 * (8 : ℤ) ^ n := by
    rw [pow_add]; norm_num; ring
  rw [h4, h3, h1]
  ring

lemma neg_eight_pow_rec (n : ℕ) :
    (-8 : ℤ) ^ (n + 4) + 4 * (-8 : ℤ) ^ (n + 3) - 256 * (-8 : ℤ) ^ (n + 1) -
      4096 * (-8 : ℤ) ^ n = 0 := by
  have h4 : (-8 : ℤ) ^ (n + 4) = 4096 * (-8 : ℤ) ^ n := by
    rw [pow_add]; norm_num; ring
  have h3 : (-8 : ℤ) ^ (n + 3) = -512 * (-8 : ℤ) ^ n := by
    rw [pow_add]; norm_num; ring
  have h1 : (-8 : ℤ) ^ (n + 1) = -8 * (-8 : ℤ) ^ n := by
    rw [pow_add]; norm_num; ring
  rw [h4, h3, h1]
  ring

lemma geom_rec (n : ℕ) :
    4 * (((8 : ℤ) ^ (n + 4) - (-8 : ℤ) ^ (n + 4)) +
        4 * ((8 : ℤ) ^ (n + 3) - (-8 : ℤ) ^ (n + 3)) -
        256 * ((8 : ℤ) ^ (n + 1) - (-8 : ℤ) ^ (n + 1)) -
        4096 * ((8 : ℤ) ^ n - (-8 : ℤ) ^ n)) = 0 := by
  linear_combination 4 * eight_pow_rec n - 4 * neg_eight_pow_rec n

lemma v_add_five (n : ℕ) :
    v (n + 5) = -2 * v (n + 4) - 16 * v (n + 3) := by
  simpa [add_assoc] using v_add_two (n + 3)

lemma v_add_four (n : ℕ) :
    v (n + 4) = -2 * v (n + 3) - 16 * v (n + 2) := by
  simpa [add_assoc] using v_add_two (n + 2)

lemma v_add_three (n : ℕ) :
    v (n + 3) = -2 * v (n + 2) - 16 * v (n + 1) := by
  simpa [add_assoc] using v_add_two (n + 1)

lemma Q_rec (n : ℕ) :
    (2 : ℤ) ^ (n + 4) * v (n + 5) + 4 * ((2 : ℤ) ^ (n + 3) * v (n + 4)) -
      256 * ((2 : ℤ) ^ (n + 1) * v (n + 2)) - 4096 * ((2 : ℤ) ^ n * v (n + 1)) = 0 := by
  have h4 : (2 : ℤ) ^ (n + 4) = 16 * (2 : ℤ) ^ n := by rw [pow_add]; norm_num; ring
  have h3 : (2 : ℤ) ^ (n + 3) = 8 * (2 : ℤ) ^ n := by rw [pow_add]; norm_num; ring
  have h1 : (2 : ℤ) ^ (n + 1) = 2 * (2 : ℤ) ^ n := by rw [pow_add]; norm_num; ring
  rw [h4, h3, h1, v_add_five, v_add_four, v_add_three]
  ring

lemma P_rec (n : ℕ) :
    P (n + 4) + 4 * P (n + 3) - 256 * P (n + 1) - 4096 * P n = 0 := by
  simp only [P_eq_geom]
  have hQ := Q_rec n
  have hG := geom_rec n
  linear_combination hQ + hG

lemma v_two : v 2 = -28 := by
  rw [v_add_two, v_zero, v_one]; norm_num

lemma v_three : v 3 = 88 := by
  rw [show 3 = 1 + 2 by norm_num, v_add_two, v_one, v_two]; norm_num

lemma v_four : v 4 = 272 := by
  rw [show 4 = 2 + 2 by norm_num, v_add_two, v_three, v_two]; norm_num

lemma two_mul_a_eq_P : ∀ n, 2 * a n = P n
  | 0 => by
    simp [a_zero, P, v_one]
  | 1 => by
    simp [a_one, P, v_two]
  | 2 => by
    simp [a_two, P, v_three]
  | 3 => by
    simp [a_three, P, v_four]
  | n + 4 => by
    have ih3 := two_mul_a_eq_P (n + 3)
    have ih1 := two_mul_a_eq_P (n + 1)
    have ih0 := two_mul_a_eq_P n
    have ha := a_add_four n
    have hP := P_rec n
    calc
      2 * a (n + 4)
        = 2 * (-4 * a (n + 3) + 256 * a (n + 1) + 4096 * a n) := by rw [ha]
      _ = -4 * (2 * a (n + 3)) + 256 * (2 * a (n + 1)) + 4096 * (2 * a n) := by ring
      _ = -4 * P (n + 3) + 256 * P (n + 1) + 4096 * P n := by rw [ih3, ih1, ih0]
      _ = P (n + 4) := by linarith [hP]

lemma a_odd_eq_sq (n : ℕ) : a (2 * n + 1) = ((2 : ℤ) ^ n * v (n + 1)) ^ 2 := by
  have hP := two_mul_a_eq_P (2 * n + 1)
  have hvs := v_sq (n + 1)
  have hPform : P (2 * n + 1) =
      (2 : ℤ) ^ (2 * n + 1) * v (2 * n + 2) + (2 : ℤ) ^ (6 * n + 6) := by
    simp only [P]
    have hneg : (-1 : ℤ) ^ (2 * n + 1) = -1 := by
      rw [pow_add, pow_mul, neg_one_sq, one_pow]
      ring
    have hpow : (2 : ℤ) ^ (3 * (2 * n + 1) + 2) = (2 : ℤ) ^ (6 * n + 5) := by
      congr 1
      ring
    rw [hneg, hpow]
    ring
  have ha : a (2 * n + 1) =
      (2 : ℤ) ^ (2 * n) * v (2 * n + 2) + (2 : ℤ) ^ (6 * n + 5) := by
    have : 2 * a (2 * n + 1) =
        (2 : ℤ) ^ (2 * n + 1) * v (2 * n + 2) + (2 : ℤ) ^ (6 * n + 6) := by
      rw [hP, hPform]
    have h2a : (2 : ℤ) ^ (2 * n + 1) = 2 * (2 : ℤ) ^ (2 * n) := by
      rw [pow_succ, mul_comm]
    have h2b : (2 : ℤ) ^ (6 * n + 6) = 2 * (2 : ℤ) ^ (6 * n + 5) := by
      rw [show 6 * n + 6 = (6 * n + 5) + 1 by ring, pow_succ]
      ring
    rw [h2a, h2b] at this
    nlinarith
  have hidx : 2 * (n + 1) = 2 * n + 2 := by ring
  rw [hidx] at hvs
  have h16 : (16 : ℤ) ^ (n + 1) = (2 : ℤ) ^ (4 * n + 4) := by
    calc (16 : ℤ) ^ (n + 1)
        = ((2 : ℤ) ^ 4) ^ (n + 1) := by norm_num
      _ = (2 : ℤ) ^ (4 * (n + 1)) := by rw [← pow_mul]
      _ = (2 : ℤ) ^ (4 * n + 4) := by congr 1
  rw [h16] at hvs
  have hcancel : (2 : ℤ) ^ (2 * n) * (2 * (2 : ℤ) ^ (4 * n + 4)) =
      (2 : ℤ) ^ (6 * n + 5) := by
    calc (2 : ℤ) ^ (2 * n) * (2 * (2 : ℤ) ^ (4 * n + 4))
        = 2 * ((2 : ℤ) ^ (2 * n) * (2 : ℤ) ^ (4 * n + 4)) := by ring
      _ = 2 * (2 : ℤ) ^ (2 * n + (4 * n + 4)) := by rw [← pow_add]
      _ = 2 * (2 : ℤ) ^ (6 * n + 4) := by congr 2; ring
      _ = (2 : ℤ) ^ ((6 * n + 4) + 1) := by rw [pow_succ]; ring
      _ = (2 : ℤ) ^ (6 * n + 5) := by congr 1
  calc
    a (2 * n + 1)
      = (2 : ℤ) ^ (2 * n) * v (2 * n + 2) + (2 : ℤ) ^ (6 * n + 5) := ha
    _ = (2 : ℤ) ^ (2 * n) * (v (n + 1) ^ 2 - 2 * (2 : ℤ) ^ (4 * n + 4)) +
          (2 : ℤ) ^ (6 * n + 5) := by
        have : v (2 * n + 2) = v (n + 1) ^ 2 - 2 * (2 : ℤ) ^ (4 * n + 4) := by
          linarith [hvs]
        rw [this]
    _ = (2 : ℤ) ^ (2 * n) * v (n + 1) ^ 2 -
          (2 : ℤ) ^ (2 * n) * (2 * (2 : ℤ) ^ (4 * n + 4)) +
          (2 : ℤ) ^ (6 * n + 5) := by ring
    _ = (2 : ℤ) ^ (2 * n) * v (n + 1) ^ 2 := by
        rw [hcancel]
        ring
    _ = ((2 : ℤ) ^ n * v (n + 1)) ^ 2 := by
        rw [mul_pow, ← pow_mul]
        congr 2
        ring

/-- oeis_113254_conjecture_0: Conjecture: a(m, 2*n+1) is a perfect square for all m,n (see A113249).
For the specific sequence A113254 (which fixes m=8), this conjecture is interpreted as:
a(2*n+1) is a perfect square for all n.
-/
theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  intro n
  rw [a_odd_eq_sq]
  exact IsSquare.sq _
