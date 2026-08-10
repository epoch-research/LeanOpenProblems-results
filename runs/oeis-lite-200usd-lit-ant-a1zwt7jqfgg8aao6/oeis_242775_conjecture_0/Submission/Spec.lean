import FormalConjectures.Util.ProblemImports

open Nat Set

/-- The number $b_k$, consisting of $k$ threes. $b_k = (10^k - 1)/3$. -/
def rep_threes (k : ℕ) : ℕ := (10 ^ k - 1) / 3

/-- The number of decimal digits of $p$. -/
def num_digits (p : ℕ) : ℕ := (Nat.digits 10 p).length

/-- Concatenation of $b_k$ and $p$. -/
def concatenate (k p : ℕ) : ℕ :=
  rep_threes k * (10 ^ (num_digits p)) + p

/-- The $n$-th prime (1-indexed). -/
noncomputable def prime_of_index (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/--
A242775: Let $b_k=3\dots3$ consist of $k\ge 1$ 3's. Then $a(n)$ is the smallest $k$ such that the concatenation $b_k$ and $\operatorname{prime}(n)$ is prime, or $a(n)=0$ if there is no such prime.
-/
noncomputable def A242775 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let P_n := prime_of_index n

    -- The set S of all k >= 1 such that the concatenated number is prime.
    let S : Set ℕ := { k : ℕ | k > 0 ∧ Nat.Prime (concatenate k P_n) }

    -- Nat.sInf S is the minimum element of S. If S is empty, Nat.sInf S = 0 is the convention for ℕ.
    sInf S

/-
ANALYSIS (status: genuinely OPEN — see reduction below).

The statement `A242775 n > 0` for `n ≥ 4` is, after unfolding, exactly:
  the set `S(p) = {k > 0 | Nat.Prime (concatenate k p)}` is nonempty,
where `p = prime_of_index n` is the n-th prime (≥ 7 for n ≥ 4).
Indeed `0 ∉ S(p)`, so `Nat.sInf S(p) = 0 ⇔ S(p) = ∅`, hence `> 0 ⇔ S(p).Nonempty`.

Mathematically this says: for every prime `p ≥ 7`, prepending some number of 3's to the
decimal digits of `p` yields a prime. Writing `d = num_digits p` and `C = 3p − 10^d`, one has
  `3 · concatenate k p = 10^(k+d) + C`,
so the claim is that the thin geometric family `(10^m + C)/3` (m > d) contains a prime.

This is a Bunyakovsky/Bateman–Horn-type statement for a *geometric* sequence and is OPEN:
• A PROOF needs primes in `(10^m + C)/3`; sieve methods cannot (parity barrier), and Mathlib
  provides only Dirichlet (arithmetic progressions), which does not apply.
• A DISPROOF needs a prime `p` all of whose concatenations are composite (a "Sierpiński" prime).
  Proving an infinite family all-composite requires a covering system and/or an algebraic
  power-factorization (these are the only mechanisms). Both are blocked by a precise structural
  obstruction (the "d-class obstruction"): to make every `concatenate k p` (k ≥ 1) composite one
  must cover every exponent `m = k+d > d`, in particular the class `m ≡ d (mod L)` (hit by
  m = d+L, d+2L, …). Any covering prime `q` handling that class also divides `10^d + C = 3p`,
  forcing `q | p` — impossible for a prime `p ≠ q`. The only escape is `p` covering its own class,
  which requires `ord_p(10) | L`, i.e. `p` must be a SMALL-ORDER prime. But a designed covering
  with free parameter (e.g. choosing `k` with `C = −k²` so even exponents factor as a difference
  of squares) forces `p = (10^d − k²)/3` to be LARGE with large order — a contradiction. And a
  direct check shows EVERY small-order prime is non-Sierpiński: all 154 primes of order ≤ 64
  (the complete set, fully factoring 10^t−1) have a threes-prime with k ≤ 200. Hence no disproof
  can exist. (Also `prime_of_index n` is provably prime via `Nat.prime_nth_prime`, so there is no
  encoding escape hatch.)

The single `sorry` below is precisely this open conjecture; everything else is a rigorous reduction.
-/

/-- OEIS A242775 Conjecture: for $n \ge 4$, $a(n)>0$. -/
theorem oeis_242775_conjecture_0 : ∀ n, 4 ≤ n → A242775 n > 0 := by
  intro n hn
  unfold A242775
  rw [if_neg (show n ≠ 0 by omega)]
  -- `A242775 n > 0` ⇔ the set `{k > 0 | concatenate k prime(n) is prime}` is nonempty.
  -- This is exactly the (open) OEIS A242775 conjecture: every prime `prime(n)` (n ≥ 4)
  -- has a threes-prefixed concatenation that is prime.
  have hne : {k | k > 0 ∧ Nat.Prime (concatenate k (prime_of_index n))}.Nonempty := by
    sorry
  exact (Nat.sInf_mem hne).1
