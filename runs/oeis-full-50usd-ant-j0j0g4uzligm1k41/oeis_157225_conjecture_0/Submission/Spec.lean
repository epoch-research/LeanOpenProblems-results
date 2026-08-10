import FormalConjectures.Util.ProblemImports

open Nat
open scoped Nat.Prime

/--
A157225: Number of ways to write the $n$-th positive odd integer in the form $p+2^x+7 \cdot 2^y$
with $p$ a prime congruent to $5 \bmod 6$ and $x,y$ positive integers.
$$a(n) = \left|\left\{(p,x,y) : p+2^x+7 \cdot 2^y=2n-1 \text{ with } p \text{ a prime congruent to } 5 \bmod 6 \text{ and } x,y \in \mathbb{Z}_{>0}\right\}\right|$$
-/
noncomputable def A157225 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let N : ℕ := 2 * n - 1
    -- Since $2^x$ and $7 \cdot 2^y$ must be less than $N$, $x$ and $y$ are effectively bounded by $\sim \log_2 N$.
    -- We use Nat.log 2 N + 1 as a safe upper bound for the range of exponents.
    let max_exp : ℕ := Nat.log 2 N + 1

    Finset.card $ (Finset.range max_exp).product (Finset.range max_exp) |>.filter (fun xy =>
      let x := xy.fst
      let y := xy.snd

      -- 1. $x, y$ are positive integers.
      1 ≤ x ∧ 1 ≤ y ∧

      let term_sum := 2 ^ x + 7 * 2 ^ y

      -- 2. $p = N - \text{term\_sum}$ must be a natural number, so term_sum < N.
      term_sum < N ∧

      let p := N - term_sum

      -- 3. $p$ must be a prime congruent to 5 mod 6.
      p.Prime ∧ p % 6 = 5
    )

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/--
Zhi-Wei Sun conjectured that $a(n)=0$ if and only if $n < 11$ or $n \in \{13, 16, 992\}$;
in other words, except for $25, 31, 1983$, any odd integer greater than $20$ can be written as the sum
of a prime congruent to $5 \bmod 6$, a positive power of $2$ and seven times a positive power of $2$.

This conjecture is FALSE. The smallest counterexample is $n = 716993899$, for which
$N = 2n-1 = 1433987797$ admits no representation $p + 2^x + 7 \cdot 2^y$ with $p$ prime
$\equiv 5 \pmod 6$ and $x,y \ge 1$ (so $A157225(716993899) = 0$), yet $716993899$ is not in
the set $\{n : n < 11\} \cup \{13, 16, 992\}$. Hence the biconditional fails at $n = 716993899$.

We prove `A157225 716993899 = 0` by exhausting the finitely many candidate pairs $(x,y)$ with
$x, y \le 30$: for each one either the side conditions fail, or the candidate $p$ has the wrong
residue mod $6$, or $p$ is composite (verified by exhibiting a proper factor via `norm_num`).
-/
theorem oeis_157225_conjecture_0.disproof :
    ¬ ∀ (n : ℕ), A157225 n = 0 ↔ n < 11 ∨ n = 13 ∨ n = 16 ∨ n = 992 := by
  intro h
  -- `A157225 716993899 = 0`: no admissible representation exists.
  have hzero : A157225 716993899 = 0 := by
    unfold A157225
    rw [if_neg (by norm_num : (716993899 : ℕ) ≠ 0)]
    have hN : (2 * 716993899 - 1 : ℕ) = 1433987797 := by norm_num
    have hlog : Nat.log 2 1433987797 = 30 :=
      Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
    simp only [hN, hlog]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro xy hxy
    replace hxy : xy ∈ (Finset.range (30 + 1)) ×ˢ (Finset.range (30 + 1)) := hxy
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hxy
    obtain ⟨x, y⟩ := xy
    obtain ⟨hx, hy⟩ := hxy
    dsimp only at hx hy ⊢
    -- Assume a representation exists and derive a contradiction.  For each concrete pair
    -- `(x, y)` we close the goal via the cheapest false hypothesis: a failing side condition,
    -- the wrong residue mod `6` (no primality test needed), or — for the genuinely dangerous
    -- pairs where `p ≡ 5 (mod 6)` — the compositeness of `p` (a small factor found by `norm_num`).
    rintro ⟨h1, h2, h3, h4, h5⟩
    revert h4
    interval_cases x <;> interval_cases y <;>
      first
        | exact absurd h5 (by decide)
        | exact absurd h3 (by decide)
        | exact absurd h1 (by decide)
        | exact absurd h2 (by decide)
        | (intro h4; exact absurd h4 (by norm_num))
  -- But the conjectured characterisation would force `716993899` into the exceptional set.
  have hmem := (h 716993899).mp hzero
  omega
