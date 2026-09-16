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
theorem oeis_17666_conjecture_0 (n : ℕ) : is_A005153 (A017666 n) → is_A005153 n := by
  sorry

lemma A017666_18 : A017666 18 = 6 := by
  dsimp [A017666]
  have h_sigma : sigma 1 18 = 39 := rfl
  rw [h_sigma]
  rfl

lemma A017666_6 : A017666 6 = 1 := by
  dsimp [A017666]
  have h_sigma : sigma 1 6 = 12 := rfl
  rw [h_sigma]
  rfl

lemma not_6_pow_2 (k : ℕ) : 6 ≠ 2^k := by
  intro h
  rcases k with _|_|_|k
  · revert h; decide
  · revert h; decide
  · revert h; decide
  · have h1 : 2 ^ (k + 3) ≥ 8 := by
      calc 2 ^ (k + 3) = 2 ^ 3 * 2 ^ k := by rw [pow_add, mul_comm]
      _ ≥ 8 * 1 := Nat.mul_le_mul_left 8 (by omega)
    omega

theorem oeis_17666_conjecture_0.disproof : ¬ (type_of% @oeis_17666_conjecture_0) := by
  intro h
  have h18 := h 18
  have h_is_A005153_A017666_18 : is_A005153 (A017666 18) := by
    dsimp [is_A005153, is_A000079]
    rw [A017666_18, A017666_6]
    use 0
    rfl
  have h_is_A005153_18 : is_A005153 18 := h18 h_is_A005153_A017666_18
  rcases h_is_A005153_18 with ⟨k, hk⟩
  rw [A017666_18] at hk
  exact not_6_pow_2 k hk
