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

lemma pow_two_ge_eight (k : ℕ) : 2^(k + 3) >= 8 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h1 : 2^(k + 1 + 3) = 2^(k + 3) * 2 := by ring
    omega

lemma pow_two_ne_six (k : ℕ) : 2^k ≠ 6 := by
  rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · have h := pow_two_ge_eight k
    omega

theorem oeis_17666_conjecture_0.disproof : ¬ ∀ (n : ℕ), is_A005153 (A017666 n) → is_A005153 n := by
  intro h
  have h18 : is_A005153 (A017666 18) → is_A005153 18 := h 18
  have h_premise : is_A005153 (A017666 18) := by
    use 0
    rfl
  have h_conclusion : is_A005153 18 := h18 h_premise
  rcases h_conclusion with ⟨k, hk⟩
  have h_val : A017666 18 = 6 := rfl
  have hk2 : 2^k = 6 := by omega
  exact pow_two_ne_six k hk2
