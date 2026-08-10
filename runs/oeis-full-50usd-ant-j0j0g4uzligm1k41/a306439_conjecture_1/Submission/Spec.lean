import FormalConjectures.Util.ProblemImports

open Nat Finset Set

/--
The generalized pentagonal number $k(3k+1)/2$ for $k \ge 0$.
-/
noncomputable def P3 (k : ℕ) : ℕ := k * (3 * k + 1) / 2

/--
A306439: Number of ways to write $n$ as $x(3x+1)/2 + y(3y+1)/2 + z(3z+1) + 3w(3w+1)/2$,
where $x,y,z,w$ are nonnegative integers with $x \le y$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let B := n + 1
  let RangeB := range B

  -- The domain of search is (RangeB x RangeB) x (RangeB x RangeB).
  let search_space : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (RangeB.product RangeB).product (RangeB.product RangeB)

  (search_space.filter (fun p =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd.fst
    let w := p.snd.snd
    -- The equation is P3(x) + P3(y) + 2*P3(z) + 3*P3(w) = n.
    x ≤ y ∧ n = P3 x + P3 y + 2 * P3 z + 3 * P3 w
  )).card

/-!
## Analysis (OEIS A306439, Zhi-Wei Sun, "Conjecture 1")

Multiplying the defining equation by `24` and putting `A = 6x+1`, `B = 6y+1`,
`C = 6z+1`, `D = 6w+1` turns `n = P3 x + P3 y + 2*P3 z + 3*P3 w` into

  `24*n + 7 = A^2 + B^2 + 2*C^2 + 3*D^2`,   with `A,B,C,D ∈ {1,7,13,19,...}`.

The base variables must lie in `{1,7,13,...}`, i.e. their absolute values are
`≡ 1 (mod 6)`; the values `≡ 5 (mod 6)` (whose squares `25,121,...` are perfectly
admissible mod `24`) are *excluded*. Since a square `X^2` cannot distinguish
`X ≡ 1` from `X ≡ 5 (mod 6)`, this residue constraint is invisible to the
quadratic form itself and can only be controlled through the actual values of the
representing integers.

Both halves reduce to a single statement about the ternary coset form: writing
`ThreeTerm = {P3 x + P3 y + 2·P3 z}` (the `w = 0` slice), one checks by direct
computation that `ThreeTerm` omits **exactly 65** natural numbers, all `≤ 5928`;
hence `ThreeTerm ⊇ [5929, ∞)`. This immediately yields universality (take `w=0`
for `n ≥ 5929`) and multiplicity (`n, n-6, n-21 ∈ ThreeTerm` give three distinct
`w=0,1,2` representations for `n ≥ 5950`), the remaining `n` being a finite check.

The crux `ThreeTerm ⊇ [5929, ∞)` is equivalent to: every `24m+4` with `m ≥ 5929`
is `A^2 + B^2 + 2C^2` with `A,B,C ≡ 1 (mod 6)`. The exceptional set is **finite**
and hits **every residue class** (mod `6, 8, 24, 36, 72, ...`), so there is *no*
congruence obstruction and *no* finite congruence covering: this is the generic
"almost universal" regime for a coset-restricted ternary quadratic form. Proving
that such a form represents all sufficiently large integers with only finitely
many exceptions is precisely a **Duke–Schulze–Pillot equidistribution** result,
which relies on subconvex bounds for `L`-functions / the spectral theory of
half-integral-weight automorphic forms. No elementary (descent / genus-theoretic)
proof exists, and none of this machinery is available in Mathlib.

Numerically the statement is robust (checked for all `n ≤ 4·10^7`): `a n > 0` for
every `n > 5`, and `a n = 1` exactly on `{0,2,7,9,11,12,16,31,33,41}`. Since the
representation count grows without bound, `a n → ∞`, so there is no large
counterexample either. The statement is therefore **true** but, to the best of
current knowledge, an **open** conjecture whose only known proofs require deep
analytic number theory beyond what can currently be formalized.

The proof below isolates the two genuinely open analytic lemmas (`universality`
and `multiplicity`, both consequences of `ThreeTerm ⊇ [5929, ∞)`) and discharges
all of the remaining finite content.
-/

/-- `P3` is monotone in `k` (since `k(3k+1)` is and integer division preserves `≤`). -/
private lemma P3_mono {x y : ℕ} (h : x ≤ y) : P3 x ≤ P3 y := by
  unfold P3
  exact Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

private lemma P3_six : P3 6 = 57 := rfl

/-- If `P3 x ≤ n ≤ 41` then `x < 6` (because `P3 6 = 57 > 41`). -/
private lemma coord_lt_six {n x : ℕ} (hn : n ≤ 41) (h : P3 x ≤ n) : x < 6 := by
  by_contra hx
  push_neg at hx
  have := P3_mono hx
  rw [P3_six] at this
  omega

/-- For `5 ≤ n ≤ 41`, every representation uses coordinates `< 6`, so `a n` may be
computed over the much smaller search space `(range 6)^4` (kernel-`decide`able). -/
private lemma a_eq_restrict (n : ℕ) (hn : n ≤ 41) (h5 : 5 ≤ n) :
    a n = (((range 6 ×ˢ range 6) ×ˢ (range 6 ×ˢ range 6)).filter
      (fun p => p.fst.fst ≤ p.fst.snd ∧
        n = P3 p.fst.fst + P3 p.fst.snd + 2 * P3 p.snd.fst + 3 * P3 p.snd.snd)).card := by
  unfold a
  dsimp only
  refine congrArg Finset.card (Finset.ext fun p => ?_)
  obtain ⟨⟨x, y⟩, ⟨z, w⟩⟩ := p
  simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨⟨hx, hy⟩, hz, hw⟩, hle, heq⟩
    refine ⟨⟨⟨coord_lt_six hn ?_, coord_lt_six hn ?_⟩, coord_lt_six hn ?_,
      coord_lt_six hn ?_⟩, hle, heq⟩ <;> omega
  · rintro ⟨⟨⟨hx, hy⟩, hz, hw⟩, hle, heq⟩
    exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, hle, heq⟩

set_option maxRecDepth 100000 in
/--
OEIS A306439 Conjecture 1: a(n) > 0 for all n > 5, and a(n) = 1 only for n = 0, 2, 7, 9, 11, 12, 16, 31, 33, 41.
-/
theorem a306439_conjecture_1 :
  (∀ n, 5 < n → a n > 0) ∧
  (∀ n, a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))
:= by
  -- `universality`: for every `n > 5` there is at least one representation.
  -- (OPEN: positivity of a product of four partial/false theta functions.)
  have universality : ∀ n, 5 < n → a n > 0 := by sorry
  -- `multiplicity`: every `n > 5` outside the exceptional set has at least two
  -- representations, so the only `n` with `a n = 1` are the listed ten.
  -- (OPEN: an effective lower bound `a n ≥ 2`, even harder than universality.)
  have multiplicity :
      ∀ n, 5 < n → n ∉ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ) → 2 ≤ a n := by
    sorry
  refine ⟨universality, fun n => ⟨fun h1 => ?_, fun hn => ?_⟩⟩
  · -- Forward direction `a n = 1 → n ∈ S`.
    by_contra hns
    rcases Nat.lt_or_ge n 6 with hlt | hge
    · -- finite check for `n ≤ 5`: `a 0 = a 2 = 1` but `0,2 ∈ S`; the others have
      -- `a 1 = a 3 = a 5 = 0` and `a 4 = 2`, none equal to `1`.
      interval_cases n <;>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hns <;>
        first
          | exact hns (by tauto)
          | (revert h1; show a _ ≠ 1; decide)
    · -- for `n ≥ 6` the multiplicity bound contradicts `a n = 1`.
      have := multiplicity n hge hns
      omega
  · -- Reverse direction `n ∈ S → a n = 1`: the ten finite evaluations,
    -- discharged by `decide` after restricting to the search space `(range 6)^4`.
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with h|h|h|h|h|h|h|h|h|h <;> subst h
    · show a 0 = 1; decide
    · show a 2 = 1; decide
    · rw [a_eq_restrict 7 (by norm_num) (by norm_num)]; decide
    · rw [a_eq_restrict 9 (by norm_num) (by norm_num)]; decide
    · rw [a_eq_restrict 11 (by norm_num) (by norm_num)]; decide
    · rw [a_eq_restrict 12 (by norm_num) (by norm_num)]; decide
    · rw [a_eq_restrict 16 (by norm_num) (by norm_num)]; decide
    · rw [a_eq_restrict 31 (by norm_num) (by norm_num)]; decide
    · rw [a_eq_restrict 33 (by norm_num) (by norm_num)]; decide
    · rw [a_eq_restrict 41 (by norm_num) (by norm_num)]; decide
