import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A275409: Number of ordered ways to write $n$ as $2w^2 + x^2 + y^2 + z^2$ with $w + x + 2y + 4z$ a square, where $w,x,y,z$ are nonnegative integers.
$$a(n) = \# \left\{(w, x, y, z) \in \mathbb{N}^4 \mid 2w^2 + x^2 + y^2 + z^2 = n, \quad w + x + 2y + 4z \text{ is a square} \right\}$$
-/
noncomputable def a (n : ℕ) : ℕ :=
  -- Define perfect square check using computable `Nat.sqrt`.
  let is_sq (k : ℕ) : Prop := k.sqrt * k.sqrt = k

  -- A safe upper bound for $w, x, y, z$ is $\lfloor\sqrt{n}\rfloor + 1$.
  let M : ℕ := n.sqrt + 1
  let R : Finset ℕ := range M

  -- The search space of ordered quadruples, structured as $w \times (x \times (y \times z))$.
  -- This allows for robust iteration over $w, x, y, z$.
  let search_space : Finset (ℕ × (ℕ × (ℕ × ℕ))) := R.product (R.product (R.product R))

  search_space.sum fun p : ℕ × (ℕ × (ℕ × ℕ)) =>
    let w := p.fst
    let x := p.snd.fst
    let y := p.snd.snd.fst
    let z := p.snd.snd.snd

    let sum_sq := 2 * w^2 + x^2 + y^2 + z^2
    let lin_comb := w + x + 2 * y + 4 * z

    -- The bounds chosen ensures that we will find all solutions (w,x,y,z) where w^2, x^2, y^2, z^2 <= n.
    -- If $2w^2 + x^2 + y^2 + z^2 = n$, then $w, x, y, z \le \sqrt{n}$, so this upper bound is sufficient.
    if sum_sq = n ∧ is_sq lin_comb
    then 1
    else 0

-- Proof snippets provided in the prompt are removed as requested, only
-- the definition needs to be present and the conjecture must be stated.
-- The definition has been corrected to rely on a mathematically sound search space bound
-- based on the fact that $w, x, y, z \le \sqrt{n}$.

/-- The set of natural numbers $n$ for which $a(n) = 0$ is conjectured to be $\{3, 10\}$. -/
def A275409_zero_set : Finset ℕ :=
  {3, 10}

/-- The set of natural numbers $n$ for which $a(n) = 1$ is conjectured to be a specific finite set. -/
def A275409_one_set : Finset ℕ :=
  {0, 2, 7, 8, 9, 12, 14, 15, 22, 23, 24, 25, 36, 39, 44, 45, 60, 87, 98, 106, 110, 111, 183}

/-!
### A faithful computable reformulation of `a`

The definition of `a` is marked `noncomputable` because elaboration of the
`if … then 1 else 0` falls back on `Classical.propDecidable` for the predicate
`is_sq lin_comb` (the `Decidable` instance is not synthesised through the
`let`-bound `is_sq`).  Since `Classical.propDecidable` agrees with the genuine
decidable instance on the truth value of the proposition, `a` has the *same*
value as the computable function `aC` below, in which the square test is written
out explicitly so the standard `DecidableEq ℕ` instance is used.
-/

/-- A computable function provably equal to `a`. -/
def aC (n : ℕ) : ℕ :=
  let M : ℕ := n.sqrt + 1
  let R : Finset ℕ := range M
  (R.product (R.product (R.product R))).sum fun p : ℕ × (ℕ × (ℕ × ℕ)) =>
    let w := p.fst
    let x := p.snd.fst
    let y := p.snd.snd.fst
    let z := p.snd.snd.snd
    if 2 * w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = n ∧
        (w + x + 2 * y + 4 * z).sqrt * (w + x + 2 * y + 4 * z).sqrt = w + x + 2 * y + 4 * z
      then 1 else 0

/-- `a` coincides with its computable reformulation `aC`.  The only difference
between the two is the `Decidable` instance used in the branch test, and the
value of an `if-then-else` depends solely on the truth value of the proposition,
not on the chosen instance. -/
theorem a_eq_aC : ∀ n : ℕ, a n = aC n := by
  intro n
  unfold a aC
  refine Finset.sum_congr rfl ?_
  intro p _
  by_cases h : (2 * p.fst ^ 2 + p.snd.fst ^ 2 + p.snd.snd.fst ^ 2 + p.snd.snd.snd ^ 2 = n ∧
      (p.fst + p.snd.fst + 2 * p.snd.snd.fst + 4 * p.snd.snd.snd).sqrt *
        (p.fst + p.snd.fst + 2 * p.snd.snd.fst + 4 * p.snd.snd.snd).sqrt =
        p.fst + p.snd.fst + 2 * p.snd.snd.fst + 4 * p.snd.snd.snd)
  · simp only [h]
  · simp only [h]

/--
Conjecture (i) from A275409:
a(n) > 0 except for n = 3, 10, and a(n) = 1 only for
n = 0, 2, 7, 8, 9, 12, 14, 15, 22, 23, 24, 25, 36, 39, 44, 45, 60, 87, 98, 106, 110, 111, 183.
-/
theorem oeis_275409_conjecture_0 :
  (∀ n : ℕ, (a n > 0 ↔ n ∉ A275409_zero_set)) ∧
  (∀ n : ℕ, (a n = 1 ↔ n ∈ A275409_one_set)) :=
by sorry
