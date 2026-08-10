import FormalConjectures.Util.ProblemImports

open Nat Finset ZMod
open scoped BigOperators

/--
T_k(b, c) is the coefficient of $x^k$ in the expansion of $(x^2 + b x + c)^k$.
$$T_k(b, c) = \sum_{i=0}^{\lfloor k/2 \rfloor} \binom{k}{i} \binom{k-i}{i} b^{k-2i} c^i$$
-/
def T_coeff (k : ℕ) (b c : ℕ) : ℚ :=
  Finset.sum (range (k / 2 + 1)) fun i =>
    (choose k i : ℚ) * (choose (k - i) i : ℚ) * (b : ℚ) ^ (k - 2 * i) * (c : ℚ) ^ i

/--
A336982: $a(n)$ is defined for $n \ge 1$.
$$a(n) = \frac{\sum_{k=0}^{n-1}(540k + 137) \cdot 3136^{n-1-k} \cdot \binom{2k}{k} \cdot T_k(2, 81) \cdot T_k(14, 81)}{2n \cdot \binom{2n}{n}}$$
The sequence is a non-negative integer sequence (nonn).
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h : n > 1 then
    let N : ℚ :=
      Finset.sum (range n) fun k =>
        ((540 * k + 137) : ℚ) *
        (3136 : ℚ) ^ (n - 1 - k) *
        (choose (2 * k) k : ℚ) *
        T_coeff k 2 81 *
        T_coeff k 14 81
    let D : ℚ := (2 * n : ℚ) * (choose (2 * n) n : ℚ)
    -- The result is conjectured to be a non-negative integer, so we cast to Int via floor and then to Nat.
    (N / D).floor.toNat
  else
    0

-- Helper function for the integer version of T_coeff, which is needed for ZMOD arithmetic.
/--
T_k(b, c) from A336982 as an integer.
It is the coefficient of $x^k$ in the expansion of $(x^2 + b x + c)^k$.
-/
def T_coeff_int (k : ℕ) (b c : ℕ) : ℤ :=
  Finset.sum (range (k / 2 + 1)) fun i =>
    (choose k i : ℤ) * (choose (k - i) i : ℤ) * (b : ℤ) ^ (k - 2 * i) * (c : ℤ) ^ i

/--
S(p) is the sum $\sum_{k=0}^{p-1} \binom{2k}{k} T_k(2, 81) T_k(14, 81)$.
-/
def S_sum (p : ℕ) : ℤ :=
  Finset.sum (range p) fun k =>
    (choose (2 * k) k : ℤ) * T_coeff_int k 2 81 * T_coeff_int k 14 81

/--
Conjecture 3: Let $p > 7$ be a prime, and let $S(p)$ denote the sum
$\sum_{k=0}^{p-1}\binom{2k}{k} T_k(2,81) T_k(14,81)$.

(1) If $(-30/p) = -1$, then $S(p) \equiv 0 \pmod{p^2}$.
(2) If $(2/p) = (p/3) = (p/5) = 1$ and $p = x^2 + 30y^2$ with $x$ and $y$ integers,
    then $S(p) \equiv (-1/p)(4x^2-2p) \pmod{p^2}$.
(3) If $(p/3) = 1$, $(2/p) = (p/5) = -1$, and $p = 3x^2 + 10y^2$ with $x$ and $y$ integers,
    then $S(p) \equiv (-1/p)(2p-12x^2) \pmod{p^2}$.
(4) If $(2/p) = 1$, $(p/3) = (p/5) = -1$, and $p = 2x^2 + 15y^2$ with $x$ and $y$ integers,
    then $S(p) \equiv (-1/p)(8x^2-2p) \pmod{p^2}$.
(5) If $(p/5) = 1$, $(2/p) = (p/3) = -1$, and $p = 5x^2 + 6y^2$ with $x$ and $y$ integers,
    then $S(p) \equiv (-1/p)(20x^2-2p) \pmod{p^2}$.
-/
theorem oeis_A336982_conjecture_3.disproof : ¬ ∀ (p : ℕ) [hp : Fact p.Prime],
  p > 7 →
  let S := S_sum p;
  let lg (a : ℤ) := legendreSym p a;
  ( -- Part (1)
    lg (-30 : ℤ) = -1 → S ≡ 0 [ZMOD (p ^ 2 : ℤ)]
  ) ∧
  ( -- Part (2)
    lg 2 = 1 ∧ lg 3 = 1 ∧ lg 5 = 1 →
    (∃ x y : ℤ, (p : ℤ) = x ^ 2 + 30 * y ^ 2) →
    ∃  x y : ℤ, (p : ℤ) = x ^ 2 + 30 * y ^ 2 ∧
    S ≡ lg (-1 : ℤ) * (4 * x ^ 2 - 2 * p.cast) [ZMOD (p ^ 2 : ℤ)]
  ) ∧
  ( -- Part (3)
    lg 3 = 1 ∧ lg 2 = -1 ∧ lg 5 = -1 →
    (∃ x y : ℤ, (p : ℤ) = 3 * x ^ 2 + 10 * y ^ 2) →
    ∃ x y : ℤ, (p : ℤ) = 3 * x ^ 2 + 10 * y ^ 2 ∧
    S ≡ lg (-1 : ℤ) * (2 * p.cast - 12 * x ^ 2) [ZMOD (p ^ 2 : ℤ)]
  ) ∧
  ( -- Part (4)
    lg 2 = 1 ∧ lg 3 = -1 ∧ lg 5 = -1 →
    (∃ x y : ℤ, (p : ℤ) = 2 * x ^ 2 + 15 * y ^ 2) →
    ∃ x y : ℤ, (p : ℤ) = 2 * x ^ 2 + 15 * y ^ 2 ∧
    S ≡ lg (-1 : ℤ) * (8 * x ^ 2 - 2 * p.cast) [ZMOD (p ^ 2 : ℤ)]
  ) ∧
  ( -- Part (5)
    lg 5 = 1 ∧ lg 2 = -1 ∧ lg 3 = -1 →
    (∃ x y : ℤ, (p : ℤ) = 5 * x ^ 2 + 6 * y ^ 2) →
    ∃ x y : ℤ, (p : ℤ) = 5 * x ^ 2 + 6 * y ^ 2 ∧
    S ≡ lg (-1 : ℤ) * (20 * x ^ 2 - 2 * p.cast) [ZMOD (p ^ 2 : ℤ)]
  ) := by
  intro h
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hc := h 13 (by norm_num : 13 > 7)
  dsimp only at hc
  have hpart3 := hc.2.2.1
  have hleg :
      legendreSym 13 (3 : ℤ) = 1 ∧ legendreSym 13 (2 : ℤ) = -1 ∧
        legendreSym 13 (5 : ℤ) = -1 := by
    constructor
    · norm_num [legendreSym]
    constructor
    · norm_num [legendreSym]
    · norm_num [legendreSym]
  have hrep : ∃ x y : ℤ, (13 : ℤ) = 3 * x ^ 2 + 10 * y ^ 2 := by
    exact ⟨1, 1, by norm_num⟩
  rcases hpart3 hleg hrep with ⟨x, y, hxy, hcong⟩
  norm_num at hxy

  have hx : x ^ 2 = 1 := by
    have hy0 : 0 ≤ y ^ 2 := sq_nonneg y
    have hy1 : y ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
    have hycases : y ^ 2 = 0 ∨ y ^ 2 = 1 := by omega
    rcases hycases with hy | hy
    · have : 13 = 3 * x ^ 2 := by nlinarith
      omega
    · nlinarith
  have hm1 : legendreSym 13 (-1 : ℤ) = 1 := by
    norm_num [legendreSym]
  rw [hm1, hx] at hcong
  rw [Int.ModEq] at hcong
  norm_num at hcong
  have hS : S_sum 13 % (169 : ℤ) = 138 := by decide
  rw [hS] at hcong
  norm_num at hcong
