import FormalConjectures.Util.ProblemImports

open Nat

/--
A157237: Number of ways to write the $n$-th positive odd integer in the form
$p + 2^x + 11 \cdot 2^y$ with $p$ a prime congruent to $1 \pmod 6$ and $x, y$ positive integers.
$$a(n)=|\{(p,x,y): p+2^x+11\cdot 2^y=2n-1 \text{ with } p \text{ a prime congruent to } 1 \pmod 6 \text{ and } x,y \in \mathbb{Z}^+\}|$$
Note: The sequence is often indexed from $n=1$, so $n$ is a positive natural number.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let N : ℕ := 2 * n - 1
  -- Upper bound for exponents $x$ and $y$. Since $2^k \le 2n-1$, $k \le \log_2(2n-1)$.
  -- $N.log2$ is $\lfloor \log_2 N \rfloor$. We can use a conservative bound.
  let B : ℕ := N.log2 + 1

  -- Range for $x$ and $y$ from 1 to B. The Finset should only contain positive integers.
  -- Finset.Icc 1 B is a safe way to get $\{1, 2, \dots, B\}$.
  let X_range : Finset ℕ := Finset.Icc 1 B
  let Y_range : Finset ℕ := Finset.Icc 1 B

  (Finset.product X_range Y_range).sum fun pair =>
    let x := pair.fst
    let y := pair.snd

    let sum_of_powers := 2 ^ x + 11 * 2 ^ y

    -- Check if $p$ is positive.
    if N > sum_of_powers then
      let p := N - sum_of_powers
      -- Prime condition: p must be prime AND p % 6 = 1.
      if Nat.Prime p ∧ p % 6 = 1 then 1 else 0
    else
      0

-- The provided initial theorems a_one, a_two, etc., are omitted here as they are proofs
-- of specific values, and the goal is to formalize the conjecture.

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/--
Conjecture A157237 (Zhi-Wei Sun, 2009):
The number of ways to write the $n$-th positive odd integer in the form $p + 2^x + 11 \cdot 2^y$,
where $p$ is a prime $\equiv 1 \pmod 6$ and $x, y \ge 1$, is zero if and only if
$n \in \{1, 2, \dots, 15, 18, 21, 24, 51, 84, 1011, 59586\}$.
-/
theorem oeis_A157237_sun_conjecture : ∀ n : ℕ, n > 0 → (a n = 0 ↔ n ≤ 15 ∨ n = 18 ∨ n = 21 ∨ n = 24 ∨ n = 51 ∨ n = 84 ∨ n = 1011 ∨ n = 59586) := by
  intro n hn
  constructor
  · -- Forward direction: `a n = 0 → n ∈ {1,…,15, 18, 21, 24, 51, 84, 1011, 59586}`.
    -- Equivalently (contrapositive): every `n` outside this finite set has `a n > 0`,
    -- i.e. every odd number `2n-1` (with `n` outside the set) is representable as
    -- `p + 2^x + 11·2^y` with `p` a prime `≡ 1 (mod 6)` and `x, y ≥ 1`.
    -- This is the open part of Zhi-Wei Sun's conjecture (OEIS A157237): a prime-existence
    -- statement in a sparse set, of the same difficulty class as the (open) problem
    -- "every large odd number is a sum of a prime and two powers of two". It is not
    -- provable by current methods (parity problem). It is verified true for all
    -- n ≤ 6·10^10, and heuristically E[a n] ~ 1.56·ln n → ∞, consistent with only
    -- finitely many exceptions.
    intro ha
    sorry
  · -- Backward direction: finite verification that `a n = 0` for each listed value.
    intro hs
    rcases hs with h | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · interval_cases n <;> (unfold a; decide)
    · unfold a; decide
    · unfold a; decide
    · unfold a; decide
    · unfold a; decide
    · unfold a; decide
    · unfold a; decide
    · -- a 59586 = 0. Kernel `decide` overflows on N = 119171, so we reduce the
      -- Finset sum to its 17×17 = 289 concrete summands and discharge each with
      -- `norm_num` (whose primality extension avoids kernel trial division).
      unfold a
      simp only [show (2 * 59586 - 1 : ℕ) = 119171 from by norm_num,
                 show (119171 : ℕ).log2 = 16 from by decide]
      rw [Finset.sum_eq_zero]
      intro pair hpair
      fin_cases hpair <;> norm_num
