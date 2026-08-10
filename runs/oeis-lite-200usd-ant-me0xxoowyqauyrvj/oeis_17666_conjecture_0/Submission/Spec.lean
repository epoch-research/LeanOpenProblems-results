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
    ¬ ∀ (n : ℕ), is_A005153 (A017666 n) → is_A005153 n := by
  have h18 : A017666 18 = 6 := by
    unfold A017666
    rw [show sigma 1 18 = 39 from by rw [sigma_one_apply]; decide]
    norm_num
  have h6 : A017666 6 = 1 := by
    unfold A017666
    rw [show sigma 1 6 = 12 from by rw [sigma_one_apply]; decide]
    norm_num
  intro h
  have key : is_A005153 18 := by
    apply h 18
    show is_A000079 (A017666 (A017666 18))
    rw [h18, h6]
    exact ⟨0, rfl⟩
  -- key : is_A000079 (A017666 18), i.e. 6 is a power of 2, contradiction
  obtain ⟨k, hk⟩ := key
  rw [h18] at hk
  -- hk : 6 = 2 ^ k
  rcases k with _ | _ | _ | k
  · simp at hk
  · simp at hk
  · norm_num at hk
  · have : 8 ≤ 2 ^ (k + 3) := by
      calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (k + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
