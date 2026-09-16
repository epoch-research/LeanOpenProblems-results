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
theorem oeis_191004_sun_refinement_conjecture :
  (∀ m : ℕ, 64 < m ∧ Odd m ∧ m ∉ ({105, 247, 255, 1105} : Finset ℕ) → odd_refinement_exists m) ∧
  (∀ m : ℕ, 8 < m ∧ Even m ∧ m ∉ ({32, 152} : Finset ℕ) → even_refinement_exists m) := by
  sorry

theorem oeis_191004_sun_refinement_conjecture.disproof : ¬ (type_of% @oeis_191004_sun_refinement_conjecture) := by
  intro h
  have h10 : 8 < 10 ∧ Even 10 ∧ 10 ∉ ({32, 152} : Finset ℕ) := by decide
  have h10_ref := h.2 10 h10
  rcases h10_ref with ⟨p, q, hp, hq, heq, hle, hjacobi⟩
  have hq_pos : 2 ≤ q := Nat.Prime.two_le hq
  have hq_eq_2 : q = 2 := by omega
  have hp8 : p = 8 := by omega
  subst hp8
  revert hp
  decide
