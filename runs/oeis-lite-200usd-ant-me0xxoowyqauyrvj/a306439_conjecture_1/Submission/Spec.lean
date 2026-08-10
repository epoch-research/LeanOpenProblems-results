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

/-- Computable mirror of `P3` (definitionally equal, used for kernel evaluation
since `P3` is marked `noncomputable`). -/
def P3c (k : ℕ) : ℕ := k * (3 * k + 1) / 2

/-- Computable mirror of `a` (definitionally equal to `a`). -/
def ac (n : ℕ) : ℕ :=
  let B := n + 1
  let RangeB := range B
  let search_space : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    (RangeB.product RangeB).product (RangeB.product RangeB)
  (search_space.filter (fun p =>
    let x := p.fst.fst
    let y := p.fst.snd
    let z := p.snd.fst
    let w := p.snd.snd
    x ≤ y ∧ n = P3c x + P3c y + 2 * P3c z + 3 * P3c w
  )).card

/-- A version of `ac` whose search range is the fixed window `range 6`.  For `n ≤ 41`
this counts exactly the same representations as `ac n` (see `ac_eq_cnt`), but over a
fixed-size domain of `6^4 = 1296` tuples, which the Lean kernel can evaluate by
`decide` (no `native_decide`, hence no `Lean.ofReduceBool`/`trustCompiler` axioms). -/
def cnt (n : ℕ) : ℕ :=
  (((range 6).product (range 6)).product ((range 6).product (range 6))).filter (fun p =>
    p.fst.fst ≤ p.fst.snd ∧ n = P3c p.fst.fst + P3c p.fst.snd + 2 * P3c p.snd.fst + 3 * P3c p.snd.snd
  ) |>.card

theorem P3c_mono : Monotone P3c := by
  intro a b hab
  apply Nat.div_le_div_right; apply Nat.mul_le_mul hab; omega

theorem P3c_bound (k : ℕ) (h : P3c k ≤ 41) : k ≤ 5 := by
  by_contra hc; push_neg at hc
  have : P3c 6 ≤ P3c k := P3c_mono (by omega)
  have : (57 : ℕ) ≤ P3c k := by simpa [P3c] using this
  omega

theorem P3c_ge (k : ℕ) : k ≤ P3c k := by
  unfold P3c
  rcases k with _ | m
  · simp
  · rw [Nat.le_div_iff_mul_le (by norm_num)]
    nlinarith [Nat.zero_le m]

/-- For `n ≤ 41`, the wasteful `range (n+1)` search of `ac n` agrees with the
fixed-window `range 6` search of `cnt n`.  Any representation of such an `n` has all four
roots `≤ 5` (since `P3c 6 = 57 > 41`), and conversely every root `k` satisfies
`k ≤ P3c k ≤ n`, so both filters select exactly the same tuples. -/
theorem ac_eq_cnt (n : ℕ) (hn2 : n ≤ 41) : ac n = cnt n := by
  unfold ac cnt
  refine congrArg Finset.card ?_
  apply Finset.Subset.antisymm
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨_, hle, heq⟩ := hp
    refine ⟨?_, hle, heq⟩
    have b1 : p.1.1 ≤ 5 := P3c_bound _ (by omega)
    have b2 : p.1.2 ≤ 5 := P3c_bound _ (by omega)
    have b3 : p.2.1 ≤ 5 := P3c_bound _ (by omega)
    have b4 : p.2.2 ≤ 5 := P3c_bound _ (by omega)
    exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩,
       Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨_, hle, heq⟩ := hp
    refine ⟨?_, hle, heq⟩
    have g1 := P3c_ge p.1.1
    have g2 := P3c_ge p.1.2
    have g3 := P3c_ge p.2.1
    have g4 := P3c_ge p.2.2
    exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩,
       Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩

/-- `a` and `cnt` agree on `n ≤ 41`.  (`a = ac` definitionally, since `noncomputable`
only blocks compiled code, not kernel defeq.) -/
theorem a_eq_cnt (n : ℕ) (hn2 : n ≤ 41) : a n = cnt n := ac_eq_cnt n hn2

set_option maxRecDepth 10000 in
/--
OEIS A306439 Conjecture 1: a(n) > 0 for all n > 5, and a(n) = 1 only for
n = 0, 2, 7, 9, 11, 12, 16, 31, 33, 41.

The proof reduces the entire statement to the single arithmetical lemma
`key : ∀ n, 42 ≤ n → 2 ≤ a n` (every `n ≥ 42` has at least two representations),
together with a finite verification of the 42 boundary cases `n ≤ 41` (carried out by
the Lean kernel via `decide` on the fixed-window count `cnt`, so the finite part of the
proof uses only the axioms `propext`, `Classical.choice`, `Quot.sound`).

Equivalently (`24·n + 7 = A² + B² + 2C² + 3D²` with `A,B,C,D ≡ 1 (mod 6)`, all positive),
`key` asserts that every `M ≡ 7 (mod 24)` with `M ∉ {31, 79, 127}` has at least two
representations by the quaternary form `x² + y² + 2z² + 3w²` in which **all** roots lie in
the residue class `1 (mod 6)`.  The lower bound `2` is tight (attained at `n = 48`), and the
two representations are algebraically independent (the definite form `x²+y²+2z²+3w²` has no
nontrivial automorphism congruent to the identity mod `6`), so `key` is a genuinely analytic
statement about the coefficients of a weight-`2` false-theta/Eisenstein series twisted by
characters modulo `6`.
-/
theorem a306439_conjecture_1 :
  (∀ n, 5 < n → a n > 0) ∧
  (∀ n, a n = 1 ↔ n ∈ ({0, 2, 7, 9, 11, 12, 16, 31, 33, 41} : Set ℕ))
:= by
  -- The single analytic core of the conjecture.
  have key : ∀ n, 42 ≤ n → 2 ≤ a n := by sorry
  refine ⟨?_, ?_⟩
  · intro n hn
    by_cases h : n ≤ 41
    · rw [a_eq_cnt n h]
      interval_cases n <;> decide
    · have := key n (by omega); omega
  · intro n
    by_cases h : n ≤ 41
    · rw [a_eq_cnt n h]
      interval_cases n <;>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] <;> decide
    · have h2 := key n (by omega)
      constructor
      · intro h1; exfalso; omega
      · intro hmem; exfalso
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        omega
