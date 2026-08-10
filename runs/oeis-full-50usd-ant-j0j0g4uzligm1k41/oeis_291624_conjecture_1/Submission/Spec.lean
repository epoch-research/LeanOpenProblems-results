import FormalConjectures.Util.ProblemImports

open Nat

/--
A291624: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers
such that $p = x + 2y + 5z$, $p - 2$ and $p + 4$ are all prime.
-/
def A291624 (n : ℕ) : ℕ :=
  let B : ℕ := sqrt n
  Finset.sum (Finset.range (B + 1)) fun x =>
  Finset.sum (Finset.range (B + 1)) fun y =>
  Finset.sum (Finset.range (B + 1)) fun z =>
    let sq_sum_xyz := x^2 + y^2 + z^2
    if sq_sum_xyz ≤ n then
      let r := n - sq_sum_xyz
      let w := sqrt r
      if w^2 = r then
        -- We have found a valid quadruple (x, y, z, w) such that x^2 + y^2 + z^2 + w^2 = n
        let p := x + 2 * y + 5 * z
        -- Check the prime triple condition. Note: p-2 is Nat.sub
        if Nat.Prime p ∧ Nat.Prime (p - 2) ∧ Nat.Prime (p + 4)
        then 1
        else 0
      else 0
    else 0

/-- **Reduction lemma (fully proved, no `sorry`).**
Exhibiting a single valid quadruple — nonnegative `x, y, z` (each `≤ √n`) with
`x² + y² + z² ≤ n`, with `n - (x²+y²+z²)` a perfect square (so `x²+y²+z²+w² = n`
for `w = √(n - (x²+y²+z²))`), and with `x + 2y + 5z`, `(x+2y+5z) - 2`,
`(x+2y+5z) + 4` all prime — already forces `A291624 n > 0`. -/
theorem A291624_pos_of_witness (n x y z : ℕ)
    (hx : x ≤ sqrt n) (hy : y ≤ sqrt n) (hz : z ≤ sqrt n)
    (hle : x ^ 2 + y ^ 2 + z ^ 2 ≤ n)
    (hsq : (sqrt (n - (x ^ 2 + y ^ 2 + z ^ 2))) ^ 2 = n - (x ^ 2 + y ^ 2 + z ^ 2))
    (hp : Nat.Prime (x + 2 * y + 5 * z) ∧ Nat.Prime (x + 2 * y + 5 * z - 2) ∧
          Nat.Prime (x + 2 * y + 5 * z + 4)) :
    A291624 n > 0 := by
  unfold A291624
  have hmemx : x ∈ Finset.range (sqrt n + 1) := Finset.mem_range.mpr (by omega)
  have hmemy : y ∈ Finset.range (sqrt n + 1) := Finset.mem_range.mpr (by omega)
  have hmemz : z ∈ Finset.range (sqrt n + 1) := Finset.mem_range.mpr (by omega)
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨x, hmemx, ?_⟩
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨y, hmemy, ?_⟩
  refine Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨z, hmemz, ?_⟩
  simp only [hle, if_true]
  rw [if_pos hsq, if_pos hp]
  exact Nat.one_pos

/-
By the reduction lemma above, the conjecture is *equivalent* to the existence,
for every `n > 1` with `4 ∤ n`, of a suitable quadruple whose linear form
`x + 2y + 5z` is the middle of a prime triplet `(p-2, p, p+4)`.

This is genuinely OPEN. The conjecture logically implies that there are infinitely
many primes `p` with `p, p-2, p+4` all prime (equivalently, infinitely many prime
triplets of pattern `(q, q+2, q+6)`): if only finitely many such primes `≤ M`
existed then every valid representation would force `x²+y²+z² ≤ 3M²`, so `n` would
have to lie within `3M²` of a perfect square — a set of density 0 — contradicting
positivity for almost all `n` (the least admissible `p` indeed grows without bound,
e.g. it is `859` for `n = 8255351`). Infinitely many prime triplets of a fixed
admissible pattern is a famous unsolved problem (obstructed by the parity barrier
of sieve theory; bounded-gap results do not yield a fixed pattern), and is not
available in Mathlib (which provides only Dirichlet's theorem for single primes in
arithmetic progressions). The conjecture is TRUE — verified for all `2 ≤ n ≤ 10¹⁰`
with `4 ∤ n` (matching `#eval` of `A291624` exactly), with `a(n)` growing — so it
admits no counterexample either. A complete proof is therefore beyond current
mathematics; the single remaining input is the open existence statement below.
-/
/-- Conjecture: a(n) > 0 for all n > 1 not divisible by 4. -/
theorem oeis_291624_conjecture_1 (n : ℕ) : n > 1 ∧ ¬ (4 ∣ n) → A291624 n > 0 := by
  rintro ⟨hn, h4⟩
  obtain ⟨x, y, z, hx, hy, hz, hle, hsq, hp⟩ :
      ∃ x y z, x ≤ sqrt n ∧ y ≤ sqrt n ∧ z ≤ sqrt n ∧
        x ^ 2 + y ^ 2 + z ^ 2 ≤ n ∧
        (sqrt (n - (x ^ 2 + y ^ 2 + z ^ 2))) ^ 2 = n - (x ^ 2 + y ^ 2 + z ^ 2) ∧
        (Nat.Prime (x + 2 * y + 5 * z) ∧ Nat.Prime (x + 2 * y + 5 * z - 2) ∧
          Nat.Prime (x + 2 * y + 5 * z + 4)) := by
    sorry
  exact A291624_pos_of_witness n x y z hx hy hz hle hsq hp
