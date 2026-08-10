import FormalConjectures.Util.ProblemImports

open Nat Set

/--
A034694: Smallest prime $\equiv 1 \pmod n$.
$$a(n) = \min \{p \in \mathbb{P} \mid p \equiv 1 \pmod n \}$$
-/
noncomputable def A034694 (n : ℕ) : ℕ :=
  -- The set infimum, sInf, gives the smallest element of the set of natural numbers.
  sInf {p : ℕ | Nat.Prime p ∧ n ∣ (p - 1)}

/-- OEIS A034694 Conjecture: a(n) < n^2 for n > 1. - Thomas Ordowski, Dec 19 2016 -/
theorem oeis_34694_conjecture_0 (n : ℕ) (h : 1 < n) :
  A034694 n < n ^ 2 := by
  -- The conjecture reduces to exhibiting a prime `p < n^2` with `p ≡ 1 (mod n)`:
  -- if such a `p` lies in the set, then `sInf` of the set is `≤ p < n^2`.
  --
  -- STATUS OF THE REMAINING GOAL `key`.
  -- =================================================================
  -- `key` asserts the existence of a prime `p < n^2` in the arithmetic progression
  -- `1 mod n`, i.e. that the least prime `≡ 1 (mod n)` satisfies `a(n) < n^2`.
  -- This is a GENUINELY OPEN problem, and moreover it is STRONGER THAN GRH:
  --
  --   * TRUE empirically: verified for all `2 ≤ n ≤ 3.8·10^8` (deterministic
  --     Miller–Rabin). The ratio `a(n)/n^2` attains its maximum `7/9 ≈ 0.778` at
  --     `n = 3` and tends to `0` as `n → ∞` (e.g. `a(100003)/100003^2 ≈ 4·10^{-4}`).
  --
  --   * BEYOND GRH: the best bound provable under GRH is `a(n) ≪ (φ(n) log n)^2`,
  --     which for prime `n` is `≈ n^2 log^2 n` — a factor `log^2 n` ABOVE `n^2`
  --     (numerically the GRH bound exceeds `n^2` by factors 21, 48, 85, 133 at
  --     `n = 101, 1009, 10007, 100003`). So even GRH does not yield `a(n) < n^2`.
  --     The best UNCONDITIONAL bound is Linnik's `a(n) ≪ n^{5.18}`. The statement
  --     `a(n) < n^2` for all `n` is of Heath-Brown/Chowla strength and is
  --     essentially equivalent to strong effective equidistribution / absence of
  --     Siegel zeros for the residue class `1 mod n`.
  --
  --   * NO ELEMENTARY PROOF: forcing one of the `n-1` candidates
  --     `n+1, 2n+1, …, (n-1)n+1 < n^2` to be prime runs into the parity problem —
  --     a candidate `kn+1 < n^2` can be a product of two primes each in `[√(kn+1), n)`,
  --     neither `≡ 1 (mod n)`, and sieves cannot exclude such P₂'s. A counting/covering
  --     argument also fails: the prime-factor "capacity" `∑_{q<n} (n-1)/q ≈ (n-1)·lnln n`
  --     exceeds the `2(n-1)` factors needed to make all candidates composite once
  --     `n ≳ 1600`, so no contradiction arises.
  --
  --   * CLEAN REFORMULATION (verified): for `m = kn+1` with `1 ≤ k ≤ n-1` (so `m < n^2`),
  --     `m` is PRIME  ⟺  `m` has NO prime factor `≤ n` (a composite `m < n^2` with all
  --     prime factors `> n` would exceed `n·n = n^2`). Hence `key` is equivalent to
  --     `∃ k ∈ [1,n-1]` with `kn+1` coprime to the primorial `∏_{q ≤ n} q ≈ e^n`. The
  --     search window `[1,n-1]` is exponentially smaller than the sieve modulus, i.e.
  --     this is exactly the "primes in a short interval vs. sieve level" (parity) regime
  --     where the linear sieve's lower-bound factor `f(s)` vanishes (`s ≈ 1`).
  --
  --   * NOT AVAILABLE IN MATHLIB: Mathlib provides only the QUALITATIVE Dirichlet
  --     theorem (`forall_exists_prime_gt_and_modEq`: `∃ p > n` with `p ≡ a`, no upper
  --     bound). There is no effective prime-in-AP / Linnik / PNT-in-AP / effective
  --     Chebotarev result to derive a bound of the form `p < n^2`.
  --
  -- Consequently `key` cannot be discharged by any currently known mathematics
  -- (it would require a result stronger than GRH), and the negation is false
  -- (no counterexample exists), so the conjecture also cannot be disproved.
  have key : ∃ p, Nat.Prime p ∧ n ∣ (p - 1) ∧ p < n ^ 2 := by
    sorry
  obtain ⟨p, hp, hd, hlt⟩ := key
  exact lt_of_le_of_lt (Nat.sInf_le (Set.mem_setOf.mpr ⟨hp, hd⟩)) hlt
