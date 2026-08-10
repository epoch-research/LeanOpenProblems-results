import FormalConjectures.Util.ProblemImports

open ArithmeticFunction Nat

/--
A017666: Denominator of sum of reciprocals of divisors of $n$.
The sum of reciprocals of divisors of $n$ is $\sigma_1(n)/n$.
The denominator of this fraction in lowest terms is $\frac{n}{\gcd(n, \sigma_1(n))}$.
-/
noncomputable def A017666 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else n / Nat.gcd n (sigma 1 n)

-- Definition for A000079: Powers of 2.
/-- A000079: Powers of 2 (including $2^0 = 1$). -/
@[reducible]
def is_A000079 (n : ℕ) : Prop := ∃ k : ℕ, n = 2^k

/--
A005153: Numbers $n$ such that the denominator of $\sigma(n)/n$ is a power of 2.
This is the interpretation that makes sense of the "dyadic rational abundancy index" comment.
-/
@[reducible]
def is_A005153 (n : ℕ) : Prop := is_A000079 (A017666 n)

/--
Conjecture: If a(n) is in A005153, then n is in A005153.
In particular, if n has dyadic rational abundancy index, i.e., a(n) is in A000079
(such as A007691 and A159907), then n is in A005153. Since every term of A005153
greater than 1 is even, any odd n such that a(n) in A005153 must be in A007691.
It is natural to ask if there exists a generalization of the indicator function for A005153,
call it m(n), such that m(n) = 1 for n in A005153, 0 < m(n) < 1 otherwise, and m(a(n)) <= m(n)
for all n. See also A050972. - _Jaycob Coleman_, Sep 27 2014
-/
-- The conjecture is FALSE. Counterexample: n = 18.
-- A017666 18 = 6 (since σ(18) = 39, gcd(18,39) = 3, 18/3 = 6).
-- A017666 6 = 1 (since σ(6) = 12, gcd(6,12) = 6, 6/6 = 1).
-- Hence is_A005153 (A017666 18) = is_A005153 6 holds (A017666 6 = 1 = 2^0),
-- but is_A005153 18 is false (A017666 18 = 6 is not a power of 2).

private lemma sig18 : sigma 1 18 = 39 := by rw [sigma_one_apply]; decide
private lemma sig6 : sigma 1 6 = 12 := by rw [sigma_one_apply]; decide

private lemma a18 : A017666 18 = 6 := by
  unfold A017666
  rw [if_neg (by norm_num), sig18]
  decide

private lemma a6 : A017666 6 = 1 := by
  unfold A017666
  rw [if_neg (by norm_num), sig6]
  decide

theorem oeis_17666_conjecture_0.disproof :
    ¬ ∀ (n : ℕ), is_A005153 (A017666 n) → is_A005153 n := by
  intro h
  have key : is_A005153 (A017666 18) → is_A005153 18 := h 18
  rw [a18] at key
  have h6 : is_A005153 6 := by
    show is_A000079 (A017666 6)
    rw [a6]
    exact ⟨0, rfl⟩
  have h18 : is_A005153 18 := key h6
  obtain ⟨k, hk⟩ := h18
  rw [a18] at hk
  have hb : k < 6 := by
    have := Nat.lt_two_pow_self (n := k)
    omega
  interval_cases k <;> simp_all
