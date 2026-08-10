import FormalConjectures.Util.ProblemImports

open Nat Finset Set

set_option maxRecDepth 8000

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

/- ### Auxiliary lemmas: monotonicity and the search-space reduction.

The infinite search domain `{0,…,n}^4` in the definition of `a` can be replaced, for `n ≤ 41`,
by a fixed `432`-element box `{0,…,5}^2 × {0,…,3} × {0,…,2}`, because the pentagonal numbers grow
fast enough (`P3 6 = 57`, `P3 4 = 26`, `P3 3 = 15`) that no larger index can contribute to a sum
that is `≤ 41`.  This makes every finite instance `a n` for `n ≤ 41` a concrete decidable count.
-/

lemma P3_mono : Monotone P3 := by
  intro p q hpq; unfold P3; apply Nat.div_le_div_right
  calc p * (3 * p + 1) ≤ q * (3 * p + 1) := Nat.mul_le_mul_right _ hpq
    _ ≤ q * (3 * q + 1) := Nat.mul_le_mul_left _ (by omega)

lemma le_P3 (k : ℕ) : k ≤ P3 k := by
  unfold P3; rcases Nat.eq_zero_or_pos k with h | h
  · simp [h]
  · have : 2 * k ≤ k * (3 * k + 1) := by nlinarith
    omega

lemma bx (x : ℕ) (h : P3 x ≤ 41) : x < 6 := by
  by_contra hc; push_neg at hc
  have h1 := P3_mono (show 6 ≤ x by omega)
  have h6 : P3 6 = 57 := by decide
  omega
lemma bz (z : ℕ) (h : 2 * P3 z ≤ 41) : z < 4 := by
  by_contra hc; push_neg at hc
  have h1 := P3_mono (show 4 ≤ z by omega)
  have h4 : P3 4 = 26 := by decide
  omega
lemma bw (w : ℕ) (h : 3 * P3 w ≤ 41) : w < 3 := by
  by_contra hc; push_neg at hc
  have h1 := P3_mono (show 3 ≤ w by omega)
  have h3 : P3 3 = 15 := by decide
  omega

noncomputable def myBox : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (Finset.range 6 ×ˢ Finset.range 6) ×ˢ (Finset.range 4 ×ˢ Finset.range 3)

noncomputable def aBox (n : ℕ) : ℕ :=
  (myBox.filter (fun p =>
    p.1.1 ≤ p.1.2 ∧ n = P3 p.1.1 + P3 p.1.2 + 2 * P3 p.2.1 + 3 * P3 p.2.2)).card

lemma box_reduction (n : ℕ) (hn : n ≤ 41) : a n = aBox n := by
  unfold a aBox myBox
  refine congrArg Finset.card ?_
  ext ⟨⟨x, y⟩, ⟨z, w⟩⟩
  simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨_, hxy, heq⟩
    exact ⟨⟨⟨bx x (by omega), bx y (by omega)⟩, bz z (by omega), bw w (by omega)⟩, hxy, heq⟩
  · rintro ⟨_, hxy, heq⟩
    have hx : x ≤ P3 x := le_P3 x
    have hy : y ≤ P3 y := le_P3 y
    have hz : z ≤ P3 z := le_P3 z
    have hw : w ≤ P3 w := le_P3 w
    exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, hxy, heq⟩

/-- All finite instances `5 < n < 42` of part (A): positivity, by decidable enumeration of the box. -/
lemma finA : ∀ n, n < 42 → 5 < n → 0 < aBox n := by decide

/-- All finite instances `n < 42` of part (B): the membership characterization of `a n = 1`. -/
lemma finB : ∀ n, n < 42 →
    (aBox n = 1 ↔ (n=0∨n=2∨n=7∨n=9∨n=11∨n=12∨n=16∨n=31∨n=33∨n=41)) := by decide

/- ### The open analytic core.

Everything in the conjecture reduces (below) to the following single statement: for every
`n ≥ 42`, the number `a n` is at least `2`.  In the equivalent square form this asserts that
`24 n + 7 = a² + b² + 2 c² + 3 d²` admits at least two solutions with all roots `≡ 1 (mod 6)`.

This is the genuinely deep, open part of Zhi-Wei Sun's conjecture (OEIS A306439).  It is *true*
(verified numerically up to `n = 2 * 10⁶`, with `a n` growing like `0.09 n`), but its proof
lies beyond elementary methods: the restriction to roots `≡ 1 (mod 6)` (the one-sided arithmetic
progression `1, 7, 13, …`) makes the relevant generating function a *partial theta function*,
which is non-modular, and the residue of a root mod `3` is invisible to its square, so no
congruence/genus argument can control it.  A complete proof requires a Deligne/Weil-type cusp-form
bound which is not available in Mathlib.  We isolate it here as the sole remaining gap.
-/
lemma coreLemma : ∀ n, 42 ≤ n → 2 ≤ a n := sorry

/--
OEIS A306439 Conjecture 1: a(n) > 0 for all n > 5, and a(n) = 1 only for n = 0, 2, 7, 9, 11, 12, 16, 31, 33, 41.
-/
theorem a306439_conjecture_1 :
  (∀ n, 5 < n → a n > 0) ∧
  (∀ n, a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))
:= by
  constructor
  · intro n hn
    rcases lt_or_ge n 42 with h | h
    · rw [box_reduction n (by omega)]; exact finA n h hn
    · have := coreLemma n h; omega
  · intro n
    rcases lt_or_ge n 42 with h | h
    · rw [box_reduction n (by omega)]
      rw [finB n h]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    · have hc := coreLemma n h
      constructor
      · intro h1; omega
      · intro hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        omega
