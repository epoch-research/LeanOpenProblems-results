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
theorem oeis_17666_conjecture_0.disproof :
    ¬ (∀ n : ℕ, is_A005153 (A017666 n) → is_A005153 n) := by
  have hs18 : sigma 1 18 = 39 := by
    rw [ArithmeticFunction.sigma_one_apply]
    decide
  have hs6 : sigma 1 6 = 12 := by
    rw [ArithmeticFunction.sigma_one_apply]
    decide
  have ha18 : A017666 18 = 6 := by
    simp [A017666, hs18]
  have ha6 : A017666 6 = 1 := by
    simp [A017666, hs6]
  have h6 : ¬ ∃ k : ℕ, 6 = 2 ^ k := by
    rintro ⟨k, hk⟩
    have hd : 3 ∣ 2 ^ k := by omega
    have hd2 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hd
    norm_num at hd2
  intro h
  have hmem : is_A005153 (A017666 18) := by
    rw [is_A005153, is_A000079, ha18, ha6]
    exact ⟨0, by norm_num⟩
  have hbad := h 18 hmem
  rw [is_A005153, is_A000079, ha18] at hbad
  exact h6 hbad
