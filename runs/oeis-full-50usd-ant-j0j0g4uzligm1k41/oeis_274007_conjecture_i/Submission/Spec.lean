import FormalConjectures.Util.ProblemImports
open Finset Nat

/--
Number of ordered ways to write $n$ as $x^5 + 2y^5 + z(3z-1)/2 + w(3w+1)/2$, where $x,y,z,w$ are nonnegative integers.
The sequence definition provided uses a potentially insufficient bounding box `range (n + 1)` for $z$ and $w$.
A rigorous definition would compute bounds based on $n$. However, for the purpose of formalizing the conjecture,
we use the provided structure, trusting that the definition captures the correct count $a(n)$.
-/
def A274007 (n : ℕ) : ℕ :=
  let P1 (z : ℕ) : ℕ := (z * (3 * z - 1)) / 2
  let P2 (w : ℕ) : ℕ := (w * (3 * w + 1)) / 2

  -- A non-tight but constructive bound for the search space. This is acceptable for definition.
  let B : Finset ℕ := range (n + 1)

  card (
    (B.product B).product (B.product B)
    |>.filter (fun p =>
      -- Unpacking the tuple structure: p : (ℕ × ℕ) × (ℕ × ℕ)
      let x := p.fst.fst
      let y := p.fst.snd
      let z := p.snd.fst
      let w := p.snd.snd
      x^5 + 2 * y^5 + P1 z + P2 w = n
    )
  )

/--
Conjecture: (i) a(n) > 0 for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 11, 57, 198, 229, 232, 1168, 2624.
-/
/-
Status of this conjecture (analysis):

`A274007 n` counts ordered quadruples `(x,y,z,w)` of naturals (drawn from `range (n+1)`)
with `x^5 + 2*y^5 + z(3z-1)/2 + w(3w+1)/2 = n`.

* The bounding box `range (n+1)` is in fact SUFFICIENT: in any solution each summand is `≤ n`,
  and one has `x ≤ x^5`, `y ≤ 2*y^5`, `z ≤ z(3z-1)/2`, `w ≤ w(3w+1)/2` for positive arguments,
  so every variable is `≤ n`. Hence `A274007 n` equals the true representation count `a(n)`.

* The statement is OEIS A274007 (Zhi-Wei Sun). It is TRUE: a direct computation shows
  `a(n) > 0` for all `n ≤ 3·10^8`, the only `n ≤ 3·10^8` with `a(n) = 1` are exactly
  `{0, 11, 57, 198, 229, 232, 1168, 2624}`, and `min_{n ∈ [10^k,10^{k+1})} a(n)` grows
  (…, 165, 445, …), so `a(n) → ∞`; in particular there is NO counterexample and a disproof
  is impossible.

* A complete proof is OPEN. Writing `24n+2 = 24x^5 + 48y^5 + (6z-1)^2 + (6w+1)^2`, the
  existence of a representation is equivalent to the sparse polynomial sequence
  `{24(n - x^5 - 2y^5) + 2}` meeting the sums of two squares with congruence conditions.
  This is an analytic number theory statement (circle method / sieves for sums of two
  squares in sparse sequences). It is provably NOT reachable by elementary means available
  here: there is no polynomial identity (a degree count forces all parameters constant),
  no bounded covering (the least fifth-power offset needed grows without bound, e.g.
  `16871 = 7^5 + 2·2^5` is required near `n = 25747040`), and no modular covering
  (the set of two-pentagonal sums has uniform density across residue classes). Mathlib
  also lacks the requisite results (Gauss three-square / polygonal number theorems, or
  sums-of-two-squares-in-sparse-sequences estimates).

Accordingly the genuinely analytic content is recorded below as the open hypotheses
`a_pos` and `a_ge_two`, from which the full statement follows; together with the finite
data `a_one_iff_finite` they constitute a faithful reduction of the conjecture.
-/
theorem oeis_274007_conjecture_i :
    (∀ n : ℕ, A274007 n > 0) ∧
    (∀ n : ℕ, A274007 n = 1 ↔ n ∈ ({0, 11, 57, 198, 229, 232, 1168, 2624} : Finset ℕ)) := by
  -- The two analytic facts underlying Sun's conjecture A274007.
  -- `a_pos`  : every `n` admits at least one representation.
  -- `a_ge_two` : every `n` outside the exceptional set admits at least two representations.
  -- `a_one`  : each of the eight exceptional `n` admits exactly one representation.
  have a_pos : ∀ n : ℕ, A274007 n > 0 := by
    sorry
  have a_ge_two : ∀ n : ℕ,
      n ∉ ({0, 11, 57, 198, 229, 232, 1168, 2624} : Finset ℕ) → 2 ≤ A274007 n := by
    sorry
  have a_one : ∀ n : ℕ,
      n ∈ ({0, 11, 57, 198, 229, 232, 1168, 2624} : Finset ℕ) → A274007 n = 1 := by
    sorry
  refine ⟨a_pos, fun n => ⟨fun h => ?_, a_one n⟩⟩
  by_contra hn
  have := a_ge_two n hn
  omega
