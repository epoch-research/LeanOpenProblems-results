import FormalConjectures.Util.ProblemImports

open Nat

/--
A157237: Number of ways to write the $n$-th positive odd integer in the form
$p + 2^x + 11 \cdot 2^y$ with $p$ a prime congruent to $1 \pmod 6$ and $x, y$ positive integers.
$$a(n)=|\{(p,x,y): p+2^x+11\cdot 2^y=2n-1 \text{ with } p \text{ a prime congruent to } 1 \pmod 6 \text{ and } x,y \in \mathbb{Z}^+\}|$$
Note: The sequence is often indexed from $n=1$, so $n$ is a positive natural number.
-/

def a_comp (n : ℕ) : ℕ :=
  let N : ℕ := 2 * n - 1
  let B : ℕ := N.log2 + 1
  let X_range : Finset ℕ := Finset.Icc 1 B
  let Y_range : Finset ℕ := Finset.Icc 1 B
  (Finset.product X_range Y_range).sum fun pair =>
    let x := pair.fst
    let y := pair.snd
    let sum_of_powers := 2 ^ x + 11 * 2 ^ y
    if N > sum_of_powers then
      let p := N - sum_of_powers
      if p.Prime ∧ p % 6 = 1 then 1 else 0
    else
      0

noncomputable def a (n : ℕ) : ℕ :=
  let N : ℕ := 2 * n - 1
  let B : ℕ := N.log2 + 1
  let X_range : Finset ℕ := Finset.Icc 1 B
  let Y_range : Finset ℕ := Finset.Icc 1 B

  (Finset.product X_range Y_range).sum fun pair =>
    let x := pair.fst
    let y := pair.snd

    let sum_of_powers := 2 ^ x + 11 * 2 ^ y

    if N > sum_of_powers then
      let p := N - sum_of_powers
      if Nat.Prime p ∧ p % 6 = 1 then 1 else 0
    else
      0

theorem oeis_A157237_sun_conjecture : ∀ n : ℕ, n > 0 → (a n = 0 ↔ n ≤ 15 ∨ n = 18 ∨ n = 21 ∨ n = 24 ∨ n = 51 ∨ n = 84 ∨ n = 1011 ∨ n = 59586) :=
by sorry

theorem oeis_A157237_sun_conjecture.disproof : ¬ (type_of% @oeis_A157237_sun_conjecture) := sorry
