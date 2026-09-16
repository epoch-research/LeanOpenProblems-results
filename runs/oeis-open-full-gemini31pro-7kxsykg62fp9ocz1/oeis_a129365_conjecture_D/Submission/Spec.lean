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
theorem oeis_a129365_conjecture_D (n p : ℕ) (hn : 0 < n) (hp : Nat.Prime p) :
  (a (n * p)).factorization p = ∑' (i : ℕ), b (n / (p ^ i)) := by
  sorry

lemma a4_eq_1 : a (2 * 2) = 1 := by rfl
lemma factor_0 : (a (2 * 2)).factorization 2 = 0 := by
  rw [a4_eq_1]
  simp

lemma b_eval_gt_1 (i : ℕ) (hi : 2 ≤ i) : b (2 / 2 ^ i) = 0 := by
  unfold b
  have h1 : 2 < 2 ^ i := by
    calc 2 < 4 := by decide
         _ = 2 ^ 2 := by decide
         _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
  rw [Nat.div_eq_of_lt h1]

lemma sum_eq_one : (∑' (i : ℕ), b (2 / 2 ^ i)) = 1 := by
  have h_zero : ∀ (i : ℕ), i ∉ Finset.range 2 → b (2 / 2 ^ i) = 0 := by
    intro i hi
    have : 2 ≤ i := by
      rw [Finset.mem_range, not_lt] at hi
      exact hi
    exact b_eval_gt_1 i this
  have h_eq := tsum_eq_sum (s := Finset.range 2) (L := SummationFilter.unconditional ℕ) h_zero
  rw [h_eq]
  rfl

theorem oeis_a129365_conjecture_D.disproof : ¬ (type_of% @oeis_a129365_conjecture_D) := by
  intro h
  have h2 := h 2 2 (by decide) (by decide)
  rw [factor_0, sum_eq_one] at h2
  revert h2
  decide
