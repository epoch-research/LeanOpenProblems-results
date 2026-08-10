import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

/-- A natural number $n$ is a perfect square if its square root squared is $n$.
This is a decidable predicate since `Nat.sqrt` is computable. -/
def Nat.is_perfect_square (n : ℕ) : Prop :=
  (Nat.sqrt n) ^ 2 = n

/-- A natural number $k$ is a generalized pentagonal number if $24k+1$ is a perfect square.
This is equivalent to $k = z(3z+1)/2$ for some integer $z$. -/
def is_generalized_pentagonal (k : ℕ) : Prop :=
  (24 * k + 1).is_perfect_square

/-- Decidability instance for `is_generalized_pentagonal`. -/
instance is_generalized_pentagonal.decidable (k : ℕ) : Decidable (is_generalized_pentagonal k) :=
  by unfold is_generalized_pentagonal Nat.is_perfect_square; infer_instance

/--
A270966: Number of ways to write $n$ as $x^2 + y^2 + z(3z+1)/2$, where $x, y$ and $z$ are integers with $0 \le x \le y$ such that $x$ or $y$ has the form $p-1$ with $p$ prime.
The number of ways is the count of valid pairs $(x, y)$ because for each such pair, $k = n - x^2 - y^2$ is a generalized pentagonal number, which corresponds uniquely to an integer $z$.
-/
def A270966 (n : ℕ) : ℕ :=
  Finset.card <|
  -- We only need to iterate $x$ and $y$ up to $n$, since $x^2+y^2 \le n$.
  (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1))).filter fun xy : ℕ × ℕ =>
    let x := xy.fst
    let y := xy.snd
    let x_sq_y_sq := x * x + y * y

    -- 1. $x^2 + y^2 \le n$ to ensure the remainder is non-negative.
    x_sq_y_sq ≤ n ∧
    -- 2. $x \le y$.
    x ≤ y ∧
    -- 3. Primality constraint: $x$ or $y$ is $p-1$, meaning $x+1$ or $y+1$ is prime.
    (Nat.Prime (x + 1) ∨ Nat.Prime (y + 1)) ∧
    -- 4. The remainder $n - (x^2 + y^2)$ must be a generalized pentagonal number.
    is_generalized_pentagonal (n - x_sq_y_sq)

/-! ### Helper lemmas for the finite (backward) direction

The definition of `A270966` uses `Nat.sqrt`, which is defined by well-founded
recursion and therefore does *not* reduce inside the kernel. To evaluate
`A270966 n` for concrete `n` using kernel-checkable `decide` (so that the proof
depends only on the permitted axioms `propext`, `Classical.choice`, `Quot.sound`),
we replace the `Nat.sqrt`-based perfect-square test by a bounded existential
search, which the kernel *can* reduce, and we restrict the iteration range so
that the computation is feasible. -/

/-- A bounded, kernel-reducible characterization of `is_generalized_pentagonal`.
If `24k+1 < C²` then `k` is generalized pentagonal iff some `w < C` has `w² = 24k+1`. -/
theorem gp_bounded (k C : ℕ) (h : 24 * k + 1 < C * C) :
    is_generalized_pentagonal k ↔ ∃ w ∈ Finset.range C, w * w = 24 * k + 1 := by
  unfold is_generalized_pentagonal Nat.is_perfect_square
  rw [pow_two, ← Nat.exists_mul_self (24 * k + 1)]
  refine ⟨?_, fun ⟨w, _, hw⟩ => ⟨w, hw⟩⟩
  rintro ⟨w, hw⟩
  refine ⟨w, ?_, hw⟩
  rw [Finset.mem_range]
  by_contra hc; push_neg at hc
  have : C * C ≤ w * w := Nat.mul_le_mul hc hc
  omega

/-- The filtered set is unchanged if we shrink the iteration square from
`range (n+1) × range (n+1)` to `range B × range B`, provided `B² > n` (so that
every pair satisfying `x²+y² ≤ n` already lies in the smaller square) and
`B ≤ n+1` (so that the smaller square is contained in the larger one). -/
theorem filter_restrict (n B : ℕ) (hBn : B ≤ n + 1) (hB : n < B * B)
    (P : ℕ × ℕ → Prop) [DecidablePred P]
    (hP : ∀ xy : ℕ × ℕ, P xy → xy.1 * xy.1 + xy.2 * xy.2 ≤ n) :
    Finset.filter P (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1)))
      = Finset.filter P (Finset.range B ×ˢ Finset.range B) := by
  apply Finset.ext
  rintro ⟨x, y⟩
  simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨_, hp⟩
    have hxy := hP (x, y) hp; simp only at hxy
    refine ⟨⟨?_, ?_⟩, hp⟩
    · by_contra h; push_neg at h; have : B * B ≤ x * x := Nat.mul_le_mul h h; omega
    · by_contra h; push_neg at h; have : B * B ≤ y * y := Nat.mul_le_mul h h; omega
  · rintro ⟨⟨hx, hy⟩, hp⟩
    exact ⟨⟨by omega, by omega⟩, hp⟩

/-- `A270966 n` equals a fully kernel-reducible finite computation: iterate over
`range B × range B` (with `B² > n`) and use the bounded perfect-square search with
cap `C` (with `24n+1 < C²`). For suitable `B, C` this makes `decide` feasible. -/
theorem A_eq_bounded (n B C : ℕ) (hBn : B ≤ n + 1) (hB : n < B * B) (hC : 24 * n + 1 < C * C) :
    A270966 n = ((Finset.range B ×ˢ Finset.range B).filter fun xy : ℕ × ℕ =>
        let x := xy.fst; let y := xy.snd; let x_sq_y_sq := x * x + y * y
        x_sq_y_sq ≤ n ∧ x ≤ y ∧ (Nat.Prime (x + 1) ∨ Nat.Prime (y + 1)) ∧
        (∃ w ∈ Finset.range C, w * w = 24 * (n - x_sq_y_sq) + 1)).card := by
  unfold A270966
  rw [filter_restrict n B hBn hB _ (fun xy hp => hp.1)]
  congr 1
  apply Finset.filter_congr
  intro xy _
  have hk : 24 * (n - (xy.1 * xy.1 + xy.2 * xy.2)) + 1 < C * C := by
    have : n - (xy.1 * xy.1 + xy.2 * xy.2) ≤ n := Nat.sub_le _ _
    omega
  simp only [gp_bounded _ C hk]

set_option maxRecDepth 10000 in
/--
Conjecture: (i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 49, 608.
-/
theorem A270966_conjecture :
  (∀ n : ℕ, n > 0 → A270966 n > 0) ∧
  (∀ n : ℕ, A270966 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) := by
  refine ⟨?_, fun n => ⟨?_, ?_⟩⟩
  · -- Part (i): a(n) > 0 for all n > 0.
    -- This is the existence (universality) part of Zhi-Wei Sun's conjecture (OEIS A270966):
    -- every positive integer n can be written as x²+y²+z(3z+1)/2 with 0≤x≤y and x+1 or y+1 prime.
    -- It is an open problem in additive number theory (no proof is known).
    intro n _hn
    sorry
  · -- Part (ii), forward direction: a(n) = 1 → n ∈ {1, 49, 608}.
    -- This is the (hard) uniqueness part of Sun's open conjecture.
    intro _h
    sorry
  · -- Part (ii), backward direction: n ∈ {1, 49, 608} → a(n) = 1.
    -- This is a finite, decidable computation, carried out via the kernel-reducible
    -- reformulation `A_eq_bounded` (with iteration cap `B` and square-root cap `C`).
    rintro (rfl | rfl | rfl)
    · rw [A_eq_bounded 1 2 6 (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [A_eq_bounded 49 8 35 (by norm_num) (by norm_num) (by norm_num)]; decide
    · rw [A_eq_bounded 608 25 121 (by norm_num) (by norm_num) (by norm_num)]; decide

