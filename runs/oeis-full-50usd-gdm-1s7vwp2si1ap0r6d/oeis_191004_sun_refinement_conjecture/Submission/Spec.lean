import FormalConjectures.Util.ProblemImports

open Nat Int

/-- The condition that $p$ is an odd prime. -/
def is_odd_prime (p : ℕ) : Prop := p.Prime ∧ p ≠ 2

/--
A191004: Number of ways to write $n = p+q+(n \bmod 2)q$, where $p$ is an odd prime and $q \le n/2$ is a prime such that $\left(\frac{q}{n}\right)=1$ if $n$ is odd, and $\left(\frac{(q+1)/2}{n+1}\right)=1$ if $n$ is even.
-/
noncomputable def A191004 (n : ℕ) : ℕ :=
  let max_q := n / 2
  Finset.sum (Finset.range (max_q + 1)) fun q : ℕ =>
    if q.Prime ∧ 2 * q ≤ n then
      let p : ℕ := if n % 2 = 1 then n - 2 * q else n - q
      if p.Prime ∧ p ≠ 2 then -- p is an odd prime
        if n % 2 = 1 then
          -- Case n is odd: J(q, n) = 1
          if jacobiSym (q : ℤ) n = 1 then 1 else 0
        else
          -- Case n is even: J((q+1)/2, n+1) = 1
          if jacobiSym (((q + 1) / 2) : ℤ) (n + 1) = 1 then 1 else 0
      else 0
    else 0

/-- Predicate for the odd case of Sun's refinement conjecture on A191004.
An odd number $m$ can be written as $p+2q$, where $p$ and $q$ are primes, and $\mathrm{JacobiSymbol}[q,p']=1$ for any prime divisor $p'$ of $m$. -/
def odd_refinement_exists (m : ℕ) : Prop :=
  ∃ p q : ℕ,
    p.Prime ∧ q.Prime ∧ m = p + 2 * q ∧
    ∀ p' ∈ m.primeFactors, jacobiSym (q : ℤ) p' = 1

/-- Predicate for the even case of Sun's refinement conjecture on A191004.
An even number $m$ can be written as $p+q$, where $p$ and $q$ are primes and $q \le m/4$, and $\mathrm{JacobiSymbol}[(q+1)/2,p']=1$ for any prime divisor $p'$ of $m+1$. -/
def even_refinement_exists (m : ℕ) : Prop :=
  ∃ p q : ℕ,
    p.Prime ∧ q.Prime ∧ m = p + q ∧ q ≤ m / 4 ∧
    ∀ p' ∈ (m + 1).primeFactors, jacobiSym (((q + 1) / 2) : ℤ) p' = 1

/-- Zhi-Wei Sun also conjectured the following refinement: Any odd number $2n+1>64$ not among $105, 247, 255, 1105$ can be written as $p+2q$, where $p$ and $q$ are primes, and $\mathrm{JacobiSymbol}[q,p']=1$ for any prime divisor $p'$ of $2n+1$; also, any even number $2n>8$ not among $32$ and $152$ can be written as $p+q$, where $p$ and $q \le n/2$ are primes, and $\mathrm{JacobiSymbol}[(q+1)/2,p']=1$ for any prime divisor $p'$ of $2n+1$. -/
theorem even_refinement_exists_10_false : ¬ even_refinement_exists 10 := by
  intro h
  rcases h with ⟨p, q, hp_prime, hq_prime, h_sum, h_q_le, h_jacobi⟩
  have hq_le2 : q ≤ 2 := h_q_le
  interval_cases q
  · exact Nat.not_prime_zero hq_prime
  · exact Nat.not_prime_one hq_prime
  · have hp8 : p = 8 := by omega
    subst hp8
    have h8_not_prime : ¬ Nat.Prime 8 := by decide
    exact h8_not_prime hp_prime

theorem oeis_191004_sun_refinement_conjecture.disproof :
  ¬ ((∀ m : ℕ, 64 < m ∧ Odd m ∧ m ∉ ({105, 247, 255, 1105} : Finset ℕ) → odd_refinement_exists m) ∧
     (∀ m : ℕ, 8 < m ∧ Even m ∧ m ∉ ({32, 152} : Finset ℕ) → even_refinement_exists m)) := by
  intro h
  have h_even := h.right
  have h_cond : 8 < 10 ∧ Even 10 ∧ 10 ∉ ({32, 152} : Finset ℕ) := by
    refine ⟨by omega, ?_, ?_⟩
    · decide
    · simp
  have h_10 := h_even 10 h_cond
  exact even_refinement_exists_10_false h_10
