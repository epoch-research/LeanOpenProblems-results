import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A321576: $a(n)$ is the smallest $b > 1$ such that $b^n - (b-1)^n$ has all divisors $d \equiv 1 \pmod n$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  if h_n : n > 0 then
    let S_n : Set ℕ :=
      { b | b > 1 ∧
          let k := b ^ n - (b - 1) ^ n -- Note: This is natural number subtraction. For n > 1 and b >= 2, b^n > (b-1)^n.
          ∀ (d : ℕ), d ∣ k → d ≡ 1 [MOD n] }
    -- sInf finds the smallest element of a set in a partial order, which is the minimum for $\mathbb{N}$.
    sInf S_n
  else
    0

/--
Conjecture: If n is prime, then a(n) = 2. Conjecture: If n is composite, then a(n) > 2.
Equivalently, for $n > 1$, $a(n)=2$ if and only if $n$ is prime.
-/
theorem oeis_321576_conjecture_prime_iff_val_two (n : ℕ) (h_n : n > 1) :
  a n = 2 ↔ Nat.Prime n :=
by sorry
