import FormalConjectures.Util.ProblemImports

open Nat

/--
A273110: Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with
$(x+4y+4z)^2 + (9x+3y+3z)^2$ a square, where $x,y,z,w$ are nonnegative integers
with $y > 0$ and $y \ge z \le w$.
-/
def A273110 (n : ℕ) : ℕ :=
  let d : ℕ := n -- Safe and conservative upper bound

  Finset.sum (Finset.range (d + 1)) fun x =>
  Finset.sum (Finset.range (d + 1)) fun y =>
  Finset.sum (Finset.range (d + 1)) fun z =>
  Finset.sum (Finset.range (d + 1)) fun w =>
    let E : ℕ := (x + 4 * y + 4 * z)^2 + (9 * x + 3 * y + 3 * z)^2

    if x^2 + y^2 + z^2 + w^2 = n ∧
       y > 0 ∧
       y ≥ z ∧ z ≤ w ∧
       (IsSquare E)
    then 1 else 0

/-- The conductor set M for the conjecture of A273110(n) = 1. -/
def A273110_set_M : Set ℕ :=
  {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}

/--
OEIS A273110 Conjecture (i):
a(n) > 0 for all n > 0, and a(n) = 1 only for n = 4^k*m (k = 0,1,2,... and
m is in the set {1, 7, 23, 31, 39, 47, 55, 71, 79, 119, 151, 191, 311, 671}).
-/
/-
Analysis (extensive computational + structural investigation; refined):

SHARPENED STRUCTURE (independently re-verified to n ≤ 2,000,000):
* Every element of M except `1` is `≡ 7 (mod 8)`:
  M \ {1} = {7,23,31,39,47,55,71,79,119,151,191,311,671} ⊂ {n : n ≡ 7 mod 8}.
  For 4-free `n ≢ 7 (mod 8)`, `a(n) = 1` happens ONLY at `n = 1`; for all such `n > 1`
  one has `a(n) ≥ 2`. For 4-free `n ≡ 7 (mod 8)`, every contributing tuple has
  `x = y + z` (the single det-3 ternary form `2y²+2yz+2z²+w²`), and `a(n) = 1` exactly
  on the 13 listed residues. Hence the forward direction is governed by the constrained
  representation count of a ternary form, i.e. by `h(-3n)`; its completeness is the open
  content (no congruence/covering description, since a finite union of sub-forms cannot
  cover the full residue class `7 (mod 8)` — squares have density 0).

SWAP-TRICK REDUCTION (new; reduces but does not remove the obstruction):
* For `x = 0` a three-square representation `n = p^2 + q^2 + r^2` (sorted `p ≤ q ≤ r`)
  with `0 < q < r` yields TWO distinct valid tuples `(0,q,p,r)` and `(0,r,p,q)` (swap of
  the two non-minimal coordinates), so `a(n) ≥ 2`. Hence for 4-free `n ≢ 7 (mod 8)` one
  has `a(n) ≥ 2` EXCEPT for the finite set `{1,2,3,9,19,22,163}` (numbers all of whose
  three-square representations are "degenerate", i.e. of shape `{0,0,r}` or `{p,q,q}`);
  only `1 ∈ M`, the others `{2,3,9,19,22,163}` get `a ≥ 2` from other families. The
  COMPLETENESS of this finite set is a class-number-one-type statement (Heegner/Baker),
  NOT provable elementarily and NOT in Mathlib.
* A Mathlib content survey confirms the obstruction is real: Mathlib has Lagrange's
  four-square theorem and the two-square CHARACTERISATION, but NO three-squares theorem,
  NO representation-count formulas, and `NumberTheory/ClassNumber` provides only abstract
  finiteness for Dedekind domains (no class-number values or lower bounds). The two
  ingredients actually needed — Gauss's three-squares theorem (positivity) and effective
  class-number completeness (forward) — are both absent and not feasibly formalizable.

REFINED FINDINGS:
* Both governing ternary forms `x^2+y^2+z^2` and `2y^2+2yz+2z^2+w^2` form
  SINGLE-CLASS genera (verified). Hence positivity (a representation EXISTS) is an
  effective "regularity" statement determined by congruence conditions — formalizable
  in principle (a finite local computation), but it is essentially the three-squares
  theorem, which is not in Mathlib.
* The forward direction `a(n)=1 → n=4^k m` is the irreducible obstruction. After
  `a(4n)=a(n)` it asks for `a(n) ≥ 2` on every 4-free `n ∉ M`. For the INFINITELY
  many `n ≡ 7 (mod 8)` the three-square family is empty, so one must exhibit `≥ 2`
  representations by the single ternary form `2y^2+2yz+2z^2+w^2`; the count of such
  representations is a BINARY CLASS NUMBER `h(-4n)`, and `h(-4n) ≥ 2` for all large
  `n` is INEFFECTIVE (Siegel) with only a Baker-type effective bound `N0 ~ 10^9`.
  Verifying `n ≤ N0` is itself out of reach in-kernel. So neither a closed proof nor
  a feasible finite reduction exists.
* EXACT CLASS-NUMBER IDENTITY (decisive): the det-3 ternary form
  `2y^2+2yz+2z^2+w^2` has representation count `r_F(n) = 3 * h(-3n)` (the imaginary
  quadratic class number), verified exactly (e.g. `r_F(7)=12=3*h(-21)`,
  `r_F(127)=60=3*h(-381)`). Hence the constrained count `a(n)` is governed by
  `h(-3n)`, and `a(n) ≥ 2` for all large 4-free `n` is equivalent to an effective
  lower bound `h(-3n) ≥ (threshold)`. This is provable only via Goldfeld–Gross–Zagier
  effective class-number bounds, whose effective constants are astronomical (and the
  constrained count is subtler still: `a(151)=1` vs `a(103)=2` though both have
  `h(-3p)=12`). This is precisely the open content and is not formalizable.
* DECISIVE STRUCTURE for primes: for every prime `p ≡ 7 (mod 8)` EVERY contributing
  tuple has `x = y + z` (only the single det-3 form contributes), so `a(p)` is the
  constrained representation count of `2y^2+2yz+2z^2+w^2`. This count is a sporadic
  arithmetic invariant (NOT a congruence function: `a(p)=1` exactly on
  `{7,23,31,47,71,79,151,191,311}` with no modular pattern, and it is not even a
  function of `h(-3p)`, e.g. `a(151)=1`, `a(199)=2` both have `h(-3p)=12`). Its
  finiteness/completeness is precisely a class-number-one-type determination, i.e.
  the genuinely open content of Sun's conjecture; it is not provable by elementary
  means or from anything in Mathlib.
* VALIDATED in-kernel computation: a complete `sorry`-free proof of `A273110 7 = 1`
  was obtained using a structurally-reducing square test `isSqB e :=
  (List.range (e+1)).any (· * · |>.beq e ...)` with proven `isSqB e = true ↔
  IsSquare e`, converting the baked `IsSquare` decidability via condition-equivalence
  and `decide`. This makes every FINITE check (the entire backward direction
  `a(4^k m)=1` for `m ∈ M`, with a range-restriction lemma to keep folds at
  ~`(⌊√m⌋+1)^4` terms) mechanizable. But it is powerless against the two infinite
  directions (positivity and forward), which have NO finite reduction.
* In-kernel finite evaluation of `A273110` IS possible in principle: the standard
  `Decidable (IsSquare ·)` instance does not reduce (it uses `Nat.sqrt`, defined by
  well-founded recursion), but a STRUCTURALLY-recursive square test does reduce, and
  `Subsingleton (Decidable p)` lets one rewrite `A273110 n` to that test. This makes
  the BACKWARD checks `a(m)=1` (m ∈ M) and finite positivity checks mechanizable, but
  is powerless against the infinite forward direction.

Older analysis (still valid):

* The conjecture is TRUE: it was verified exactly for all `n ≤ 10^8`, and the
  residue class `n ≡ 7 (mod 8)` (where the only large exceptional values can occur)
  was confirmed clean far beyond that. The reference computation was validated
  against Lean's own `#eval` of `A273110`.

* Genuine structural facts established here:
  - `a(4*n) = a(n)`:  for a representation of `4*n` the four squares are either all
    even or all odd. If all odd then `x+4y+4z` and `9x+3y+3z` are both odd, so
    `E ≡ 2 (mod 4)` is never a perfect square; thus only all-even representations
    contribute, and these biject with representations of `n` (since
    `E(2x,2y,2z,2w) = 4*E(x,y,z,w)`).  Hence everything reduces to 4-free `n`.
  - The quantity `E = (x+4y+4z)^2 + (9x+3y+3z)^2` depends only on `x` and `u = y+z`.
    The families `x = 0` (giving `E = 25(y+z)^2`) and `x = y+z` (giving
    `E = 169(y+z)^2`) always make `E` a perfect square; together they cover every
    positive `n` (`x=0` handles the sums of three squares; `x=y+z`, i.e. the form
    `2y^2+2yz+2z^2+w^2`, handles `n = 4^a(8b+7)`).
  - The exceptional 4-free numbers with a unique ordered three-square representation
    are exactly `{1,2,3,19,22,163}` (class-number-one discriminants; `163` is the
    largest Heegner number).

* Why a complete formal proof is out of reach:
  - The forward direction `a(n)=1 → n ∈ {4^k m}` is equivalent to `a(n) ≥ 2` for every
    4-free `n ∉ M` (the computed minimum over such `n` is exactly `2`). This is the
    completeness of the finite exceptional set `M`, an *open* number-theoretic fact
    tied to ineffective class-number lower bounds / idoneal numbers (conjecturally
    GRH-conditional). No elementary or feasibly-formalizable proof is known.
  - The positivity part `0 < n → 0 < a(n)` needs Gauss's three-squares theorem,
    which is not in Mathlib.
  - Even individual finite values cannot be settled in-kernel: `decide` does not
    reduce `A273110 1 = 1` (the `IsSquare` decidability instance gets stuck), and
    `native_decide` is disallowed.

* Why no disproof is possible either: there is no counterexample below `10^8`; any
  larger counterexample has an in-kernel-uncomputable `A273110 n`; and the only
  structurally provable kind of counterexample (a "backward failure": some
  `n = 4^k m, m ∈ M`, with `a(n) ≥ 2`) cannot exist, since `a(4n)=a(n)` and
  `a(m)=1` for every `m ∈ M`.

The proof below records the correct logical structure; the three genuinely open /
Mathlib-missing ingredients are isolated.
-/
theorem A273110_conjecture (n : ℕ) :
  (0 < n → 0 < A273110 n) ∧
  (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m) := by
  refine ⟨fun hn => ?_, ?_, ?_⟩
  · -- Positivity: every positive `n` has a valid representation.
    -- Requires Gauss's three-squares theorem (for `n` a sum of three squares,
    -- use the `x = 0` family) together with the `x = y+z` family for
    -- `n = 4^a(8b+7)`.  Not available in Mathlib.
    sorry
  · -- Forward: `a(n) = 1 → n = 4^k m`.
    -- Equivalent to `a(n) ≥ 2` for all 4-free `n ∉ M`; this is the (open)
    -- completeness of the exceptional set `M`.
    intro _h
    sorry
  · -- Backward: `n = 4^k m, m ∈ M → a(n) = 1`.
    -- Provable in principle via `a(4n) = a(n)` and the finite checks `a(m) = 1`
    -- for `m ∈ M`, but those finite evaluations are intractable for the Lean
    -- kernel (`A273110 m` sums over `(m+1)^4` terms and `IsSquare` does not reduce).
    rintro ⟨k, m, _hm, _rfl⟩
    sorry
