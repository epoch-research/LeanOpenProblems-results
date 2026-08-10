import FormalConjectures.Util.ProblemImports

open Nat BigOperators

/--
The numerator product $\prod_{i=1}^{n} (3n+i-1)! \cdot (i-1)!$ for the sequence A352656.
-/
def A352656_num_prod (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).prod fun i =>
    (3 * n + i - 1).factorial * (i - 1).factorial

/--
The denominator product $\prod_{i=1}^{n} (2n+i-1)! \cdot (n+i-1)!$ for the sequence A352656.
-/
def A352656_den_prod (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).prod fun i =>
    (2 * n + i - 1).factorial * (n + i - 1).factorial

/--
A352656: The number of lozenge tilings of a semiregular hexagon of side lengths $n, n, 2n, n, n$ and $2n$;
equivalently, the number of plane partitions whose solid Young diagram fits inside an $n \times n \times 2n$ box.
The formula used is:
$$a(n) = \prod_{i=1}^{n} \frac{(3n+i-1)! \cdot (i-1)!}{(2n+i-1)! \cdot (n+i-1)!}$$
-/
def A352656 (n : ℕ) : ℕ :=
  if n = 0 then
    1 -- a(0) = 1
  else
    A352656_num_prod n / A352656_den_prod n

/--
The superfactorial function S(n) = Product_{k = 0..n-1} k! with S(0) = 1.
-/
def superfactorial (n : ℕ) : ℕ :=
  (Finset.range n).prod fun k => k.factorial

/--
The superfactorial ratio $F(a, b, c) := \frac{S(a) S(b) S(c) S(a+b+c)}{S(a+b) S(a+c) S(b+c)}$.
This is known to be an integer, which justifies the use of ℕ division.
-/
def F (a b c : ℕ) : ℕ :=
  let num := superfactorial a * superfactorial b * superfactorial c * superfactorial (a + b + c)
  let den := superfactorial (a + b) * superfactorial (a + c) * superfactorial (b + c)
  num / den


theorem superfactorial_pos (n : ℕ) : 0 < superfactorial n := by
  induction n with
  | zero =>
    rw [superfactorial]
    decide
  | succ n ih =>
    rw [superfactorial, Finset.prod_range_succ]
    apply Nat.mul_pos ih (Nat.factorial_pos n)

theorem F_zero (b c : ℕ) : F 0 b c = 1 := by
  unfold F
  simp only [zero_add]
  have h_sf_zero : superfactorial 0 = 1 := rfl
  rw [h_sf_zero, one_mul]
  have h_pos : 0 < superfactorial b * superfactorial c * superfactorial (b + c) := by
    apply Nat.mul_pos
    · apply Nat.mul_pos (superfactorial_pos b) (superfactorial_pos c)
    · apply superfactorial_pos
  exact Nat.div_self h_pos

theorem F_zero_b (a c : ℕ) : F a 0 c = 1 := by
  unfold F
  simp only [add_zero, zero_add]
  have h_sf_zero : superfactorial 0 = 1 := rfl
  rw [h_sf_zero, mul_one]
  have h_den : superfactorial a * superfactorial (a + c) * superfactorial c =
               superfactorial a * superfactorial c * superfactorial (a + c) := by
    ac_rfl
  rw [h_den]
  have h_pos : 0 < superfactorial a * superfactorial c * superfactorial (a + c) := by
    apply Nat.mul_pos
    · apply Nat.mul_pos (superfactorial_pos a) (superfactorial_pos c)
    · apply superfactorial_pos
  exact Nat.div_self h_pos

theorem F_zero_c (a b : ℕ) : F a b 0 = 1 := by
  unfold F
  simp only [add_zero]
  have h_sf_zero : superfactorial 0 = 1 := rfl
  rw [h_sf_zero, mul_one]
  have h_den : superfactorial (a + b) * superfactorial a * superfactorial b =
               superfactorial a * superfactorial b * superfactorial (a + b) := by
    ac_rfl
  rw [h_den]
  have h_pos : 0 < superfactorial a * superfactorial b * superfactorial (a + b) := by
    apply Nat.mul_pos
    · apply Nat.mul_pos (superfactorial_pos a) (superfactorial_pos b)
    · apply superfactorial_pos
  exact Nat.div_self h_pos
/--
%C A352656 Conjecture 1: the supercongruences F(a*p^r,b*p^r,c*p^r) == F(a*p^(r-1),b*p^(r-1),c*p^(r-1))^p (mod p^(4*r))
hold for all primes p, where r is a positive integer and a, b and c are nonnegative integers.
(We interpret the undefined 'k' in the original OEIS entry as 'r').
-/
theorem oeis_A352656_conjecture_1 (p : ℕ) (hp : p.Prime) (r : ℕ) (hr : 0 < r) (a b c : ℕ) :
  (F (a * p ^ r) (b * p ^ r) (c * p ^ r) : ℤ) ≡
  (F (a * p ^ (r - 1)) (b * p ^ (r - 1)) (c * p ^ (r - 1)) : ℤ) ^ p
    [ZMOD (p ^ (4 * r) : ℤ)] :=
by
  rcases a with _ | a
  · simp only [zero_mul, F_zero, Int.ofNat_one, one_pow]; rfl
  rcases b with _ | b
  · simp only [zero_mul, F_zero_b, Int.ofNat_one, one_pow]; rfl
  rcases c with _ | c
  · simp only [zero_mul, F_zero_c, Int.ofNat_one, one_pow]; rfl
  -- Now we have a > 0, b > 0, c > 0.
  sorry
