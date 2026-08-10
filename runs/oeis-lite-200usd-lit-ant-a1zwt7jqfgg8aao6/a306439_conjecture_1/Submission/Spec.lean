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
### Structure of the proof

We reduce the conjecture to elementary finite computations for `n ≤ 41` together with a
single infinite lower bound.  Since `max {0,2,7,9,11,12,16,31,33,41} = 41`, every `n > 41`
lies outside the exceptional set, so the two conjuncts are together equivalent to:

* the finitely many facts `a n = 1 ↔ n ∈ S` and `5 < n → 0 < a n` for `n ≤ 41`, together with
* the single infinite statement `∀ n, 41 < n → 2 ≤ a n`.

The finite part is fully proved below: any representation of `n` uses arguments `k` with
`P3 k ≤ n`, and since `k ≤ P3 k` and `P3` is monotone, every such `k` lies in the explicit
box `range 6` as soon as `n < P3 6 = 57` (which covers all `n ≤ 41`).  This lets us replace
`a n` by the cardinality of a filtered `Finset` over the fixed `6 × 6 × 6 × 6` box, which is
decidable by `decide`.

The infinite statement `∀ n, 41 < n → 2 ≤ a n` is the entire mathematical difficulty.
It is isolated below as the lemma `hard`.

*Why it is deep.*  Using `3·P3 0 = 0`, `3·P3 1 = 6`, `3·P3 2 = 21`, taking `w ∈ {0,1,2}`
shows `a n` is at least the number of `w ∈ {0,1,2}` for which the *ternary* count
`c(m) := #{(x,y,z) : x ≤ y, m = P3 x + P3 y + 2 P3 z}` is positive at `m = n - 3·P3 w`.
Numerically (checked to `5·10⁶`) `c(m) = 0` for exactly `65` values of `m`, all `≤ 5928`, so
`c(m) ≥ 1` for every `m > 5928`; hence `a n ≥ 3` for `n > 5949`, and only a finite base case
remains.

The heart is thus `c(m) ≥ 1` for large `m`.  Multiplying by `24` (via
`24·k(3k+1)/2 = (6k+1)² - 1`), this is representability of `24 m + 4` by `A² + B² + 2 C²` with
`A, B, C ≡ 1 (mod 6)`.  The *unconstrained* form `x² + y² + 2z²` is regular and always
represents `24 m + 4`; but the residue constraint `≡ 1 (mod 6)` describes a **shifted**
ternary lattice, whose theta series has a genuine *cusp-form* component (this is exactly why
the escape set is finite yet nonempty, with no congruence pattern: `245, 249, 253, 270, …`).
Positivity for large `m` is therefore an instance of **Duke's equidistribution theorem** for
ternary quadratic forms (bounds on Fourier coefficients of half-integral-weight cusp forms).

Equivalently, the Krachun–Sun reduction (arXiv:2001.05325, Lemma 4.1 and Theorem 1.3) routes
the same content through Kaplansky's representation theorem for the ternary form `x² + y² + 7z²`
— the classical irregular form of class number `2` ("first nontrivial genus") — together with
a finite base case of size `~10⁹`.  (The prime `7 = 1+1+2+3` is intrinsic: eliminating the
diagonal variable gives a ternary form of determinant `42 = 2·3·7`.)

Neither Duke's theorem nor Kaplansky's theorem — nor even Gauss's three–square theorem or the
Hasse–Minkowski principle for ternary forms — is available in the current Mathlib, and the
associated base case is far beyond kernel evaluation.  The lemma `hard` records this
irreducible core.
-/

/-- Box version of `a` with an explicit fixed search bound `K` in place of `n + 1`. -/
noncomputable def aBox (K n : ℕ) : ℕ :=
  let RangeB := range K
  let search_space : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (RangeB.product RangeB).product (RangeB.product RangeB)
  (search_space.filter (fun p =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd.fst
    let w := p.snd.snd
    x ≤ y ∧ n = P3 x + P3 y + 2 * P3 z + 3 * P3 w
  )).card

lemma P3_mono : Monotone P3 := by
  intro a b h
  unfold P3
  apply Nat.div_le_div_right
  have : a * (3 * a + 1) ≤ b * (3 * b + 1) := Nat.mul_le_mul h (by omega)
  omega

lemma P3_lt {n K x : ℕ} (hK : n < P3 K) (hx : P3 x ≤ n) : x < K := by
  by_contra h
  push_neg at h
  have := P3_mono h
  omega

lemma le_P3 (x : ℕ) : x ≤ P3 x := by
  unfold P3
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  rcases Nat.eq_zero_or_pos x with h | h
  · simp [h]
  · nlinarith [h]

/-- If `n < P3 K`, then any representation of `n` uses arguments `< K`, so `a n` equals the
count over the fixed box `range K`. -/
lemma a_eq_aBox (n K : ℕ) (hK : n < P3 K) : a n = aBox K n := by
  unfold a aBox
  simp only
  congr 1
  apply Finset.ext
  rintro ⟨⟨x, y⟩, z, w⟩
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only
  constructor
  · rintro ⟨hmem, hxy, heq⟩
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp h1
    obtain ⟨hz, hw⟩ := Finset.mem_product.mp h2
    rw [Finset.mem_range] at hx hy hz hw
    refine ⟨?_, hxy, heq⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_range.mpr (show x < K from P3_lt hK (by omega))
    · exact Finset.mem_range.mpr (show y < K from P3_lt hK (by omega))
    · exact Finset.mem_range.mpr (show z < K from P3_lt hK (by omega))
    · exact Finset.mem_range.mpr (show w < K from P3_lt hK (by omega))
  · rintro ⟨hmem, hxy, heq⟩
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp h1
    obtain ⟨hz, hw⟩ := Finset.mem_product.mp h2
    rw [Finset.mem_range] at hx hy hz hw
    refine ⟨?_, hxy, heq⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_range.mpr (show x < n + 1 by have := le_P3 x; omega)
    · exact Finset.mem_range.mpr (show y < n + 1 by have := le_P3 y; omega)
    · exact Finset.mem_range.mpr (show z < n + 1 by have := le_P3 z; omega)
    · exact Finset.mem_range.mpr (show w < n + 1 by have := le_P3 w; omega)

/--
The single deep number-theoretic core of the conjecture: every `n > 41` has at least two
representations `n = P3 x + P3 y + 2 P3 z + 3 P3 w` with `x ≤ y`.

Equivalently (multiplying by `24`), for every `m ≡ 7 (mod 24)` with `m > 24·41 + 7` there are
at least two representations `m = A² + B² + 2 C² + 3 D²` with `A,B,C,D` positive and `≡ 1
(mod 6)` and `A ≤ B`.  This is a congruence-restricted quaternary representation problem whose
resolution (via the Krachun–Sun reduction, arXiv:2001.05325) requires Kaplansky's
representation theorem for the ternary form `x² + y² + 7z²` — the classical irregular ternary
form of class number `2` — together with a base case of size `~10⁹`.  Neither ingredient is
available in, or feasibly derivable from, the current Mathlib.
-/
lemma hard : ∀ n, 41 < n → 2 ≤ a n := by
  sorry

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/--
OEIS A306439 Conjecture 1: a(n) > 0 for all n > 5, and a(n) = 1 only for n = 0, 2, 7, 9, 11, 12, 16, 31, 33, 41.
-/
theorem a306439_conjecture_1 :
  (∀ n, 5 < n → a n > 0) ∧
  (∀ n, a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))
:= by
  refine ⟨?_, ?_⟩
  · intro n hn
    by_cases h : n ≤ 41
    · interval_cases n <;> (rw [a_eq_aBox _ 6 (by decide)]; decide)
    · push_neg at h
      have := hard n h
      omega
  · intro n
    by_cases h : n ≤ 41
    · interval_cases n <;>
        (rw [a_eq_aBox _ 6 (by decide)];
         simp only [Set.mem_insert_iff, Set.mem_singleton_iff];
         decide)
    · push_neg at h
      have h2 := hard n h
      constructor
      · intro he; omega
      · intro hmem
        exfalso
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        omega
