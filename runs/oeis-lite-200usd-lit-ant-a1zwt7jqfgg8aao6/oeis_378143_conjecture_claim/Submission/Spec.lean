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
  intro n hn
  -- KEY OBSERVATION: `4 ^ (2 ^ n) + 1 = 2 ^ (2 ^ (n+1)) + 1 = F_{n+1}`, the `(n+1)`-th Fermat
  -- number.  These are prime for `n = 0, 1, 2, 3` (namely `5, 17, 257, 65537`), so the LEFT
  -- disjunct `Nat.Prime (4 ^ (2 ^ n) + 1)` holds outright for all `n ≤ 3`, with no need to
  -- inspect the hypothesis `hn` at all.
  match n with
  | 0 => exact Or.inl (by norm_num)
  | 1 => exact Or.inl (by norm_num)
  | 2 => exact Or.inl (by norm_num)
  | 3 => exact Or.inl (by norm_num)
  | (k + 4) =>
      -- For `n = k + 4 ≥ 4`, `F_{n+1} = F_5, F_6, …` is composite, and the hypothesis
      -- `hn : Nat.Prime (10 ^ (2 ^ (k+4)) + 1)` is the OPEN CORE of this conjecture.  The
      -- implication holds vacuously for every `n` for which `10 ^ (2 ^ n) + 1` is composite,
      -- so discharging the statement for `n ≥ 4` is equivalent to proving that
      -- `10 ^ (2 ^ n) + 1` is composite for all `n ≥ 2` (verified `n = 2,…,16`, e.g.
      -- `73 ∣ 10^4+1`, `17 ∣ 10^8+1`, `353 ∣ 10^16+1`).
      --
      -- That statement is the assertion that there are NO generalized Fermat primes base 10
      -- beyond `11 = 10^(2^0)+1` and `101 = 10^(2^1)+1`.
      --
      -- This is the EXACT base-10 analogue of the (open) Fermat-prime problem: writing
      -- `aₙ = 10^(2^n)+1`, the telescoping identity `10^(2^n)-1 = 9·∏_{k<n} aₖ` gives the
      -- Fermat-type recursion `a_{n+1} = aₙ(aₙ-2)+2` and pairwise coprimality of the `aₙ` —
      -- structurally identical to `F_{n+1} = (Fₙ-1)²+1`, `∏_{k<n} Fₖ = Fₙ-2`.  Deciding whether
      -- all `aₙ`, `n ≥ 2`, are composite is therefore as hard as deciding whether all Fermat
      -- numbers `Fₙ`, `n ≥ 5`, are composite — a FAMOUS UNSOLVED PROBLEM (Mathlib accordingly
      -- provides only Pépin's primality TEST and pairwise coprimality, no compositeness result).
      -- It is genuinely OPEN:
      --   * `Φ_{2^{n+1}}(10) = 10^(2^n)+1` is an irreducible cyclotomic value (no polynomial
      --     factorisation: `Φ_{2^k}(x) = x^{2^{k-1}}+1` is irreducible over `ℤ`);
      --   * no Aurifeuillian factorisation exists (base-10 Aurifeuillian needs `5 ∣` exponent,
      --     but the exponent `2^n` is a pure power of two);
      --   * no covering set exists — every prime `p ∣ 10^(2^n)+1` has `ord_p(10) = 2^{n+1}`,
      --     so each prime divides exactly ONE term, ruling out a finite covering system;
      --   * the three primalities `10^(2^n)+1`, `4^(2^n)+1`, `6^(2^n)+1` are arithmetically
      --     independent — the premise forces no residue obstruction on the disjuncts.
      -- Resolving it is unknown for ANY base and is beyond current mathematics.
      sorry
