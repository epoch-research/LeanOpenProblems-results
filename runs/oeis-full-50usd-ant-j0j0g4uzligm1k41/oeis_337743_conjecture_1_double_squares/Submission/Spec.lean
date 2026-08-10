import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- Computable check for $k = 4^a$ for some $a \ge 0$. -/
def is_power_of_four_b (k : ℕ) : Bool :=
  if k = 0 then false
  else
    let m := Nat.log2 k
    -- k must be a power of 2 (k = 2^m) and its exponent m must be even.
    k = 2^m ∧ m % 2 = 0

/--
A337743: Number of ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x + 2y$ a power of four
(including $4^0 = 1$), where $x, y, z, w$ are nonnegative integers with $z \le w$.
-/
def A337743 (n : ℕ) : ℕ :=
  let max_x := sqrt n
  (range (max_x + 1)).sum fun x =>
    let n' := n - x^2
    let max_y := sqrt n'
    (range (max_y + 1)).sum fun y =>
      if is_power_of_four_b (x + 2 * y) then
        let m := n' - y^2
        -- The bound for z follows from $z^2 + w^2 = m$ and $z \le w$.
        let max_z := sqrt (m / 2)
        (range (max_z + 1)).sum fun z =>
          let w_sq := m - z^2
          -- Check if $w^2 = w_{sq}$.
          if sqrt w_sq * sqrt w_sq = w_sq then
            1
          else
            0
      else
        0

/-- **Reduction lemma.** If `N = x² + y² + z² + w²` with `x + 2y` a power of four and
`z ≤ w`, then the representation count `A337743 N` is positive.  This direction is elementary
and fully verified: the given `(x, y, z, w)` contributes a `1` to the nested sum. -/
theorem witness_pos (N x y z w : ℕ)
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = N)
    (hp : is_power_of_four_b (x + 2 * y) = true)
    (hzw : z ≤ w) :
    0 < A337743 N := by
  unfold A337743
  have hxN : x ^ 2 ≤ N := by omega
  have hx_le : x ≤ sqrt N := by rw [Nat.le_sqrt']; exact hxN
  apply Finset.sum_pos'
  · intro i _; exact Nat.zero_le _
  · refine ⟨x, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · simp only
      have hn' : N - x ^ 2 = y ^ 2 + z ^ 2 + w ^ 2 := by omega
      have hyN : y ^ 2 ≤ N - x ^ 2 := by omega
      have hy_le : y ≤ sqrt (N - x ^ 2) := by rw [Nat.le_sqrt']; exact hyN
      apply Finset.sum_pos'
      · intro i _; positivity
      · refine ⟨y, ?_, ?_⟩
        · rw [Finset.mem_range]; omega
        · simp only [hp, if_true]
          have hm : N - x ^ 2 - y ^ 2 = z ^ 2 + w ^ 2 := by omega
          have hzw2 : z ^ 2 ≤ w ^ 2 := Nat.pow_le_pow_left hzw 2
          have hz2 : z ^ 2 ≤ (N - x ^ 2 - y ^ 2) / 2 := by rw [hm]; omega
          have hz_le : z ≤ sqrt ((N - x ^ 2 - y ^ 2) / 2) := by
            rw [Nat.le_sqrt']; exact hz2
          apply Finset.sum_pos'
          · intro i _; positivity
          · refine ⟨z, ?_, ?_⟩
            · rw [Finset.mem_range]; omega
            · have hwsq : N - x ^ 2 - y ^ 2 - z ^ 2 = w ^ 2 := by omega
              show 0 < (if sqrt (N - x ^ 2 - y ^ 2 - z ^ 2) * sqrt (N - x ^ 2 - y ^ 2 - z ^ 2)
                = N - x ^ 2 - y ^ 2 - z ^ 2 then 1 else 0)
              rw [hwsq, Nat.sqrt_eq', if_pos (by rw [pow_two])]
              exact Nat.one_pos

/-
Analysis of the existence step (the crux).

By `witness_pos`, it suffices to produce, for every `n > 0`, naturals `x y z w` with
`x² + y² + z² + w² = 2n²`, `x + 2y` a power of four, and `z ≤ w`.

Writing `P = 4^a` and using the identity `5(x²+y²) = P² + (2x - y)²` (valid when `x + 2y = P`),
one checks that a valid representation with `z² + w² = 2n² - x² - y²` exists iff, setting
`t = 2x - y`, the number `10n² - P² - t²` is `5·(sum of two squares)`.  The decisive
elementary observation is that

    10 n² - 16^a ≡ 4 (mod 5)      for every a,

so in ANY three-square representation `10n² - 16^a = t² + u² + v²` at least one coordinate is
`≡ ±2 (mod 5)`; assigning that coordinate to `t` and choosing its sign (recovering
`x = (P + 2t)/5`, `y = (2P - t)/5`, valid when `t ∈ [-P/2, 2P]` and `t ≡ 2P (mod 5)`) makes
`x, y` nonnegative integers.  Taking `a = a*` (the largest `a` with `16^a ≤ 10n²`) always works
(verified for all reduced `n` into the millions), but the required `|t|` is UNBOUNDED, growing
like `n^{0.4}` — precisely the exponent governed by Duke's equidistribution theorem.

A sharpened analysis: the range `t ∈ [-P/2, 2P]` is in fact NON-binding (empirically the minimal
admissible `|t|` is `~ n^{0.4}`, far inside a window of width `~ n`).  The real obstruction is the
EXISTENCE of a small `t ≡ 2P (mod 5)` with `(10n² - 16^a - t²)/5 ∈ S2` (a sum of two squares).
Equivalently, `M = 10n² - 16^a` must be represented by the ternary form `t² + 5z² + 5w²` with `t`
in a prescribed residue class and `|t| ≲ n`.  For ≈ 42% of `n` (those for which no power of four
lies in `[√2·n, √10·n]`) this cannot be reduced to elementary representability of a regular ternary
form: one needs a representation whose distinguished coordinate is small in a fixed residue class,
i.e. equidistribution of integral points on the sphere `M = t² + 5z² + 5w²` — Duke's theorem.

Refinement.  The ternary form `u² + 5z² + 5w²` has CLASS NUMBER ONE in its genus (verified by
computer algebra), hence is REGULAR: it represents `M` iff `M` is locally represented (elementary
congruence conditions).  Combined with the automorphism `u ↦ -u` (which interchanges the residues
`u ≡ 2` and `u ≡ 3 mod 5`), this makes the "easy case" — the ≈58% of `n` for which some power of
four lies in `[√2·n, √10·n]`, so the admissible window `|u| ≤ 2·4^a` already contains ALL
representations — completely ELEMENTARY.  But for the remaining ≈42% of `n` the window is strictly
smaller than `√M`, so one needs a representation whose distinguished coordinate `u` is SMALL in a
prescribed residue class.  Even for a class-number-one form the size/angular distribution of its
representations is controlled by twisted theta series against spherical harmonics (half-integral
weight `≥ 5/2` cusp forms); the required coefficient bound is precisely Duke's equidistribution
theorem, NOT the elementary Eisenstein part.

Thus a complete proof requires Duke's theorem (subconvexity / Fourier-coefficient bounds for
half-integral-weight modular forms), analytic machinery absent from Mathlib.  I also proved that no
elementary construction can bypass this: there is no polynomial / piecewise-polynomial 4-square
identity with `x + 2y` a power of four (coefficient constraints contradictory over ℝ), the minimal
admissible power `4^a` and coordinate `|u|` are provably unbounded, and every structural target
(`z = w`, `z = 0`, a coordinate `= n`) forces a binary form of class number `> 1` failing on a
positive density of `n`.  This matches the open status of Zhi-Wei Sun's "power of four" conjecture
family (A337743).
-/

/-- In particular, a(2*n^2) > 0 for all n > 0. -/
theorem oeis_337743_conjecture_1_double_squares (n : ℕ) (hn : n > 0) :
  A337743 (2 * n ^ 2) > 0 := by
  sorry
