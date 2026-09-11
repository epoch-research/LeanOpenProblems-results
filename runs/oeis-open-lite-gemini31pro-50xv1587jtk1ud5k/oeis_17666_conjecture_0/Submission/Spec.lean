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

theorem A017666_18 : A017666 18 = 6 := by
  dsimp [A017666]
  decide

theorem A017666_6 : A017666 6 = 1 := by
  dsimp [A017666]
  decide

theorem oeis_17666_conjecture_0.disproof : ¬ (type_of% @oeis_17666_conjecture_0) := by
  push_neg
  use 18
  constructor
  · use 0
    change A017666 (A017666 18) = 2^0
    rw [A017666_18, A017666_6]
    rfl
  · intro k hk
    have hk' : 6 = 2^k := by
      calc
        6 = A017666 18 := A017666_18.symm
        _ = 2^k := hk
    have h1 : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
    rcases h1 with rfl | rfl | rfl | h3
    · revert hk'; decide
    · revert hk'; decide
    · revert hk'; decide
    · have h4 : 2^k ≥ 2^3 := Nat.pow_le_pow_right (by decide) h3
      omega
