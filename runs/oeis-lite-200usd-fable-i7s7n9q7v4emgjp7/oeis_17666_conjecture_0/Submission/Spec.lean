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

theorem sigma_one_18 : sigma 1 18 = 39 := by
  rw [ArithmeticFunction.sigma_one_apply]
  decide

theorem sigma_one_6 : sigma 1 6 = 12 := by
  rw [ArithmeticFunction.sigma_one_apply]
  decide

theorem A017666_18 : A017666 18 = 6 := by
  rw [A017666]
  simp [sigma_one_18]

theorem A017666_6 : A017666 6 = 1 := by
  rw [A017666]
  simp [sigma_one_6]

/--
Disproof of the conjecture: $n = 18$ is a counterexample.
We have $\sigma(18) = 39$, $\gcd(18, 39) = 3$, so $A017666(18) = 6$, which is not a
power of 2, hence $18 \notin A005153$. But $\sigma(6) = 12$, $\gcd(6,12) = 6$, so
$A017666(6) = 1 = 2^0$, hence $A017666(18) = 6 \in A005153$.
-/
theorem oeis_17666_conjecture_0.disproof :
    ¬ ∀ (n : ℕ), is_A005153 (A017666 n) → is_A005153 n := by
  intro h
  have h6 : is_A005153 (A017666 18) := by
    rw [A017666_18]
    exact ⟨0, by rw [A017666_6]; rfl⟩
  have h18 := h 18 h6
  rw [is_A005153, is_A000079, A017666_18] at h18
  obtain ⟨k, hk⟩ := h18
  have hlt : k < 3 := by
    by_contra hge
    push_neg at hge
    have : (2 : ℕ)^3 ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hge
    omega
  interval_cases k <;> omega
