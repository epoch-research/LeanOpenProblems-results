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

/-!
OEIS A270966 Conjecture:
(i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 49, 608.
-/

/-- For `k ≤ 608` the predicate `is_generalized_pentagonal k` is equivalent to a
bounded (kernel-reducible) search: `24 * k + 1` is a square of some `w < 121`.  This lets
us evaluate `A270966 n` for small `n` by `decide`, since `Nat.sqrt` itself does not reduce
in the kernel. -/
lemma gp_iff_bdd (k : ℕ) (hk : k ≤ 608) :
    is_generalized_pentagonal k ↔ ∃ w ∈ Finset.range 121, w ^ 2 = 24 * k + 1 := by
  unfold is_generalized_pentagonal Nat.is_perfect_square
  constructor
  · intro h
    refine ⟨Nat.sqrt (24 * k + 1), ?_, h⟩
    rw [Finset.mem_range]
    have : Nat.sqrt (24 * k + 1) ≤ Nat.sqrt 14593 := Nat.sqrt_le_sqrt (by omega)
    have h121 : Nat.sqrt 14593 < 121 := by rw [Nat.sqrt_lt']; norm_num
    omega
  · rintro ⟨w, _, hw⟩
    have : Nat.sqrt (24 * k + 1) = w := by rw [← hw, pow_two]; exact Nat.sqrt_eq w
    rw [this, hw]

/-- The bounded, kernel-reducible reformulation of the counting predicate. -/
def Qpred (n : ℕ) (xy : ℕ × ℕ) : Prop :=
  let x := xy.1; let y := xy.2; let s := x * x + y * y
  s ≤ n ∧ x ≤ y ∧ (Nat.Prime (x + 1) ∨ Nat.Prime (y + 1)) ∧
  ∃ w ∈ Finset.range 121, w ^ 2 = 24 * (n - s) + 1

instance (n : ℕ) : DecidablePred (Qpred n) := by unfold Qpred; infer_instance

/-- For `n ≤ 608`, `A270966 n` equals the cardinality of the bounded predicate over a
small square grid `[0,b) × [0,b)`, provided `b` bounds the coordinates of any valid pair. -/
lemma A270966_eq_bdd (n b : ℕ) (hn : n ≤ 608) (hbn : b ≤ n + 1)
    (hbdd : ∀ x y : ℕ, x * x + y * y ≤ n → x < b ∧ y < b) :
    A270966 n = ((Finset.range b ×ˢ Finset.range b).filter (Qpred n)).card := by
  unfold A270966
  rw [Finset.product_eq_sprod]
  rw [Finset.filter_congr (q := Qpred n) (fun xy _ => by
    simp only [Qpred]; rw [gp_iff_bdd _ (by omega)])]
  congr 1
  apply Finset.ext
  rintro ⟨x, y⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Qpred]
  constructor
  · rintro ⟨⟨_, _⟩, hs, hrest⟩
    exact ⟨hbdd x y hs, hs, hrest⟩
  · rintro ⟨⟨hx, hy⟩, hs, hrest⟩
    exact ⟨⟨by omega, by omega⟩, hs, hrest⟩

/--
Positivity part of Sun's conjecture: every positive integer admits at least one
representation of the required kind.  Equivalently, `24 * n + 1` is represented by the
ternary form `24 * x ^ 2 + 24 * y ^ 2 + w ^ 2` in such a way that one of `x, y` is one
less than a prime.  The unconditional representability by this ternary form is known
(the form is regular), but the additional *prime-shift* condition makes this an open
problem of Zhi-Wei Sun.
-/
theorem A270966_pos (n : ℕ) (hn : n > 0) : A270966 n > 0 := by
  sorry

/--
The counting refinement of Sun's conjecture: for every `n ≥ 609` there are at least
two admissible representations, so the value `1` is attained only for the sporadic
`n ∈ {1, 49, 608}`.  This finiteness statement is the deepest part of the conjecture
and is currently open.
-/
theorem A270966_ge_two (n : ℕ) (hn : n ≠ 1) (hn' : n ≠ 49) (hn'' : n ≠ 608)
    (hpos : n > 0) : A270966 n ≥ 2 := by
  sorry

set_option maxRecDepth 10000

/-- The three sporadic values indeed have a unique representation.  Fully proved by
reduction to a bounded, kernel-reducible computation. -/
theorem A270966_anchors : A270966 1 = 1 ∧ A270966 49 = 1 ∧ A270966 608 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [A270966_eq_bdd 1 2 (by norm_num) (by norm_num)
      (by intro x y h; constructor <;> nlinarith)]; decide
  · rw [A270966_eq_bdd 49 8 (by norm_num) (by norm_num)
      (by intro x y h; constructor <;> nlinarith)]; decide
  · rw [A270966_eq_bdd 608 25 (by norm_num) (by norm_num)
      (by intro x y h; constructor <;> nlinarith)]; decide

theorem oeis_270966_conjecture_i :
  (∀ n : ℕ, n > 0 → A270966 n > 0) ∧
  (∀ n : ℕ, n > 0 → (A270966 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608)) := by
  obtain ⟨h1, h49, h608⟩ := A270966_anchors
  refine ⟨fun n hn => A270966_pos n hn, fun n hn => ⟨fun h => ?_, ?_⟩⟩
  · -- If `A270966 n = 1` then `n` cannot be `≥ 2`, forcing it into the sporadic set.
    by_contra hmem
    push_neg at hmem
    obtain ⟨hne1, hne49, hne608⟩ := hmem
    have := A270966_ge_two n hne1 hne49 hne608 hn
    omega
  · rintro (rfl | rfl | rfl)
    · exact h1
    · exact h49
    · exact h608
