import FormalConjectures.Util.ProblemImports
open Nat Finset

/--
A129365: $a(n) = A092287(n)/A129364(n)$.
$$a(n) = \frac{\prod_{j=1}^n \prod_{k=1}^n \gcd(j,k)}{\prod_{k=1}^n (\lfloor n/k \rfloor!)^k}$$
-/
def a (n : ℕ) : ℕ :=
  -- A092287(n) = Product Product gcd(j,k)
  let numerator : ℕ := (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k
  -- A129364(n) = Product (floor(n/k)!)^k
  let denominator : ℕ := (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k

  -- The conjecture guarantees that the division is exact.
  numerator / denominator

-- Helper function for A004125, b(n) = floor(n/2)
def b (n : ℕ) : ℕ := n / 2

-- Note: `(m.factorization p)` is the exponent of p in the prime factorization of m,
-- corresponding to ordp(m, p).

/--
oeis_a129365_conjecture_D: Let b(n) = A004125(n). Then
ordp(a(n*p),p) = b(n) + b(floor(n/p)) + b(floor(n/p^2)) + b(floor(n/p^3)) + ....

The conjecture as stated (with the function `b n = n / 2` used in this file, rather
than A004125) is false. For example, at `n = 2`, `p = 2` we have `a 4 = 1`, so
`ordp(a 4, 2) = 0`, while the right-hand side `∑' i, b (2 / 2 ^ i) = b 2 = 1`.
-/
theorem oeis_a129365_conjecture_D.disproof :
    ¬ ∀ (n p : ℕ), 0 < n → Nat.Prime p →
      (a (n * p)).factorization p = ∑' (i : ℕ), b (n / (p ^ i)) := by
  intro h
  have key := h 2 2 (by norm_num) (by norm_num)
  have ha : a (2 * 2) = 1 := by decide
  have hsum : (∑' (i : ℕ), b (2 / (2 ^ i))) = 1 := by
    rw [tsum_eq_single 0]
    · rfl
    · intro i hi
      have h2 : 2 ≤ 2 ^ i := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hi)
      show (2 / 2 ^ i) / 2 = 0
      have hle : 2 / 2 ^ i ≤ 1 := Nat.div_le_of_le_mul (by omega)
      exact Nat.div_eq_of_lt (lt_of_le_of_lt hle (by norm_num))
  rw [ha, hsum, Nat.factorization_one] at key
  simp at key

