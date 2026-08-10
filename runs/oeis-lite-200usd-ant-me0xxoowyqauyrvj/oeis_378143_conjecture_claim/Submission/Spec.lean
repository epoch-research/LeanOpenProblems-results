import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A378143: $a(n)$ is the smallest prime of the form $(2p)^{2^n} + 1$ for some prime $p$.
-/
noncomputable def A378143 (n : ℕ) : ℕ :=
  sInf { k : ℕ | Nat.Prime k ∧ ∃ p : ℕ, Nat.Prime p ∧ k = (2 * p) ^ (2 ^ n) + 1 }

/--
The conjecture is equivalent to the claim that a(n) is not 10^(2^n) + 1 for any n,
which in turn is equivalent to the claim that, if 10^(2^n) + 1 is prime,
then either 4^(2^n) + 1 or 6^(2^n) + 1 is prime. - Charles R Greathouse IV, Nov 17 2024
-/
theorem oeis_378143_conjecture_claim :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) := by
  intro n hC
  match n with
  -- For n = 0,1,2,3 the number 4^(2^n)+1 = F_{n+1} is one of the four Fermat
  -- primes 5, 17, 257, 65537, so the left disjunct holds unconditionally.
  | 0 => exact Or.inl (by norm_num)
  | 1 => exact Or.inl (by norm_num)
  | 2 => exact Or.inl (by norm_num)
  | 3 => exact Or.inl (by norm_num)
  -- For n ≥ 4, 4^(2^n)+1 = F_{n+1} is composite (F_5,… are composite) and
  -- 6^(2^n)+1 is composite for the relevant n, so the conjecture reduces to:
  --   "10^(2^n)+1 is composite for every n ≥ 2."
  --
  -- Writing C_n := 10^(2^n)+1, one checks C_{n+1} = (C_n − 1)^2 + 1 and that the
  -- C_n are PAIRWISE COPRIME — structurally identical to the Fermat numbers
  -- F_n = 2^(2^n)+1.  Consequently every prime divides at most one C_n, so no
  -- finite covering system can prove all C_n (n ≥ 2) composite; and the
  -- cyclotomic polynomial Φ_{2^(n+1)} is irreducible with rad(10) ∤ 2^n, so no
  -- algebraic / Aurifeuillian factorization exists either.  Proving "C_n is
  -- composite for all n ≥ 2" is therefore exactly as hard as proving that there
  -- are only finitely many Fermat primes — a problem open since the 1600s.
  --
  -- Hence this n ≥ 4 case is the genuinely OPEN kernel of the conjecture; it
  -- cannot be discharged by currently-known mathematics.
  | (k + 4) => sorry
