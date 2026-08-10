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

lemma helper2 (n : ℕ) : 2 < 2^(n+2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h1 : 2^(n + 1 + 2) = 2^(n+2) * 2 := rfl
    have : 2^(n+2) > 0 := by positivity
    omega

lemma helper (b' : ℕ) (h : b' ≠ 0) : b (2 / 2^b') = 0 := by
  rcases b' with _ | _ | n
  · contradiction
  · rfl
  · unfold b
    rw [Nat.div_eq_of_lt (helper2 n)]

lemma sum_helper : ∑' (i : ℕ), b (2 / (2 ^ i)) = 1 := by
  have h_single : ∑' (i : ℕ), b (2 / (2 ^ i)) = b (2 / (2 ^ 0)) := by
    apply tsum_eq_single 0
    intro b' hb'
    exact helper b' hb'
  rw [h_single]
  rfl

lemma a4_eq : a 4 = 1 := by decide

lemma lhs_helper : (a (2 * 2)).factorization 2 = 0 := by
  have : a (2 * 2) = 1 := a4_eq
  rw [this, Nat.factorization_one]
  rfl

-- Note: `(m.factorization p)` is the exponent of p in the prime factorization of m,
-- corresponding to ordp(m, p).

/--
oeis_a129365_conjecture_D: Let b(n) = A004125(n). Then
ordp(a(n*p),p) = b(n) + b(floor(n/p)) + b(floor(n/p^2)) + b(floor(n/p^3)) + ....
-/
theorem oeis_a129365_conjecture_D.disproof :
  ¬ (∀ (n p : ℕ) (hn : 0 < n) (hp : Nat.Prime p),
    (a (n * p)).factorization p = ∑' (i : ℕ), b (n / (p ^ i))) := by
  intro h
  have h_spec := h 2 2 (by decide) Nat.prime_two
  rw [lhs_helper, sum_helper] at h_spec
  nomatch h_spec
