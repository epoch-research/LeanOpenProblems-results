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
lemma A017666_eighteen : A017666 18 = 6 := by
  unfold A017666
  rw [if_neg (by decide : 18 ≠ 0)]
  have : sigma 1 18 = 39 := rfl
  rw [this]
  have : Nat.gcd 18 39 = 3 := rfl
  rw [this]

lemma A017666_six : A017666 6 = 1 := by
  unfold A017666
  rw [if_neg (by decide : 6 ≠ 0)]
  have : sigma 1 6 = 12 := rfl
  rw [this]
  have : Nat.gcd 6 12 = 6 := rfl
  rw [this]

lemma is_A000079_one : is_A000079 1 := ⟨0, rfl⟩

lemma not_is_A000079_six : ¬ is_A000079 6 := by
  rintro ⟨k, hk⟩
  have hdiv : 3 ∣ 2 ^ k := by
    rw [← hk]
    decide
  have : 3 ∣ 2 := (by decide : Nat.Prime 3).dvd_of_dvd_pow hdiv
  exact absurd this (by decide : ¬ 3 ∣ 2)

theorem oeis_17666_conjecture_0.disproof :
    ¬∀ (n : ℕ), is_A005153 (A017666 n) → is_A005153 n := by
  intro h
  have h18 := h 18
  have h6 : is_A005153 (A017666 18) := by
    rw [A017666_eighteen]
    unfold is_A005153
    rw [A017666_six]
    exact is_A000079_one
  have hn18 : ¬ is_A005153 18 := by
    unfold is_A005153
    rw [A017666_eighteen]
    exact not_is_A000079_six
  exact hn18 (h18 h6)
