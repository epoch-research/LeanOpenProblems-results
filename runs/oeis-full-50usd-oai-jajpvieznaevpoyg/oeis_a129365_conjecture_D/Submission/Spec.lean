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
-/
theorem oeis_a129365_conjecture_D.disproof :
  ¬ ∀ (n p : ℕ), 0 < n → Nat.Prime p →
    (a (n * p)).factorization p = ∑' (i : ℕ), b (n / (p ^ i)) := by
  intro h
  have hp : Nat.Prime 2 := by norm_num [Nat.prime_two]
  have h2 := h 2 2 (by norm_num) hp
  have ha : a (2 * 2) = 1 := by decide
  have ht : (∑' (i : ℕ), b (2 / (2 ^ i))) = 1 := by
    rw [tsum_eq_single 0]
    · norm_num [b]
    · intro i hi
      cases i with
      | zero => contradiction
      | succ i =>
        simp [b]
        exact Nat.div_lt_self (by norm_num) (Nat.one_lt_pow (Nat.succ_ne_zero i) (by norm_num))
  rw [ha, ht] at h2
  norm_num at h2
