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
/-
Reduction of the conjecture to the (open) finiteness of base-10 generalized Fermat primes.

For `n ≤ 3` the number `4 ^ (2 ^ n) + 1 = 2 ^ (2 ^ (n+1)) + 1 = F_{n+1}` is a Fermat prime
(`5, 17, 257, 65537`), so the conclusion holds unconditionally.  For `n = k + 4` the
implication holds iff the hypothesis fails, i.e. iff `10 ^ (2 ^ (k+4)) + 1` is composite; this
is the open kernel `no_base10_gfn_prime`.
-/
private theorem oeis_378143_conjecture_claim_of_kernel
    (no_base10_gfn_prime : ∀ k : ℕ, ¬ Nat.Prime (10 ^ (2 ^ (k + 4)) + 1)) :
    ∀ (n : ℕ),
      Nat.Prime (10 ^ (2 ^ n) + 1) →
        Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) := by
  intro n hp
  match n with
  | 0 => left; norm_num
  | 1 => left; norm_num
  | 2 => left; norm_num
  | 3 => left; norm_num
  | (k + 4) => exact absurd hp (no_base10_gfn_prime k)

theorem oeis_378143_conjecture_claim :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) := by
  apply oeis_378143_conjecture_claim_of_kernel
  -- Open kernel: `10 ^ (2 ^ (k+4)) + 1` is composite for all `k`, i.e. there are no base-10
  -- generalized Fermat primes `10 ^ (2 ^ n) + 1` for `n ≥ 4`.  This is an open problem
  -- (finiteness of base-10 generalized Fermat primes), unreachable by covering congruences
  -- or algebraic factorization.
  sorry
