import FormalConjectures.Util.ProblemImports

open Nat

/--
A271510: Number of ordered ways to write $n$ as $x^2 + y^2 + z^2 + w^2$ with $x \ge y \ge 0$, $z \ge 0$ and $w \ge 0$ such that $x^2 + 8y^2 + 16z^2$ is a square.
-/
def A271510 (n : ℕ) : ℕ :=
  -- Define the decidable predicate for being a perfect square in ℕ.
  let is_square (k : ℕ) : Prop := k.sqrt * k.sqrt = k

  -- The maximum value for any variable is $\lfloor\sqrt{n}\rfloor$.
  let bound := n.sqrt
  let R : Finset ℕ := Finset.range (bound + 1)

  -- The search space is the Cartesian product R x R x R x R, structured as (((ℕ × ℕ) × ℕ) × ℕ).
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) := R.product R |>.product R |>.product R

  Finset.card $ search_space.filter fun p =>
    -- Decompose the nested product tuple p = (((x, y), z), w)
    let x := p.fst.fst.fst
    let y := p.fst.fst.snd
    let z := p.fst.snd
    let w := p.snd

    -- Constraint 1: sum of squares equals n
    x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
    -- Constraint 2: $x \ge y$
    x ≥ y ∧
    -- Constraint 3: $x^2 + 8y^2 + 16z^2$ is a square.
    is_square (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2)

-- A standard definition for "is a square" on ℕ
def is_square (k : ℕ) : Prop := ∃ m : ℕ, k = m^2

/--
`A271510.witness_pos`:  If `(x, y, z, w)` is a concrete witness — i.e. it lies within the
search bound `n.sqrt`, has `x² + y² + z² + w² = n`, satisfies `x ≥ y`, and makes
`x² + 8y² + 16z²` a perfect square (in the `Nat.sqrt` sense used inside `A271510`) — then
`A271510 n > 0`.

This is the rigorous bridge between the existence of a single representation and the
positivity of the counting function `A271510`. -/
theorem A271510.witness_pos (n x y z w : ℕ)
    (hx : x ≤ n.sqrt) (hy : y ≤ n.sqrt) (hz : z ≤ n.sqrt) (hw : w ≤ n.sqrt)
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n)
    (hxy : x ≥ y)
    (hsq : (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt
        = x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) :
    0 < A271510 n := by
  unfold A271510
  simp only
  rw [Finset.card_pos]
  refine ⟨(((x, y), z), w), ?_⟩
  rw [Finset.mem_filter]
  refine ⟨?_, hsum, hxy, hsq⟩
  simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> omega

/-- A square never exceeds `n`'s root: from `a ^ 2 ≤ n` we get `a ≤ n.sqrt`. -/
theorem A271510.le_sqrt_of_sq_le {a n : ℕ} (h : a ^ 2 ≤ n) : a ≤ n.sqrt := by
  rw [Nat.le_sqrt]
  nlinarith [sq_nonneg a]

/--
`A271510.witness_pos'`:  the same bridge stated in mathematically-natural terms, with the
search-bound side conditions discharged automatically from `x² + y² + z² + w² = n`. -/
theorem A271510.witness_pos' (n x y z w : ℕ)
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n)
    (hxy : x ≥ y)
    (hsq : is_square (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2)) :
    0 < A271510 n := by
  obtain ⟨m, hm⟩ := hsq
  have hsq' : (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt
      = x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2 := by
    rw [hm, Nat.sqrt_eq']; ring
  have hx : x ≤ n.sqrt :=
    A271510.le_sqrt_of_sq_le (by nlinarith [sq_nonneg y, sq_nonneg z, sq_nonneg w])
  have hy : y ≤ n.sqrt :=
    A271510.le_sqrt_of_sq_le (by nlinarith [sq_nonneg x, sq_nonneg z, sq_nonneg w])
  have hz : z ≤ n.sqrt :=
    A271510.le_sqrt_of_sq_le (by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg w])
  have hw : w ≤ n.sqrt :=
    A271510.le_sqrt_of_sq_le (by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z])
  exact A271510.witness_pos n x y z w hx hy hz hw hsum hxy hsq'

/--
`A271510.WitnessSpec n` :  the assertion that `n` admits a representation
`n = x² + y² + z² + w²` with `x ≥ y` and `x² + 8y² + 16z²` a perfect square.
This is *equivalent* to `0 < A271510 n` (via `A271510.witness_pos'`). -/
def A271510.WitnessSpec (n : ℕ) : Prop :=
    ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ x ≥ y ∧
      is_square (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2)

/--
**Scaling reduction.**  A witness for `m` yields a witness for `k² · m`, obtained
by scaling all four coordinates by `k`.  This is the rigorous content of the
4-adic / square-multiple descent: the quadratic constraint `x²+8y²+16z²=□` is
homogeneous of degree 2, so it is preserved (the square root scales by `k`), and
the sum of squares scales by `k²`. -/
theorem A271510.witnessSpec_scale (k m : ℕ) (h : A271510.WitnessSpec m) :
    A271510.WitnessSpec (k ^ 2 * m) := by
  obtain ⟨x, y, z, w, hsum, hxy, s, hs⟩ := h
  refine ⟨k * x, k * y, k * z, k * w, ?_, ?_, k * s, ?_⟩
  · have e : (k * x) ^ 2 + (k * y) ^ 2 + (k * z) ^ 2 + (k * w) ^ 2
        = k ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by ring
    rw [e, hsum]
  · exact Nat.mul_le_mul_left k hxy
  · have e : (k * x) ^ 2 + 8 * (k * y) ^ 2 + 16 * (k * z) ^ 2
        = k ^ 2 * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) := by ring
    rw [e, hs]; ring

/--
**Reduction to the squarefree case.**  Since every `n` factors as `b² · a` with `a`
squarefree (`Nat.sq_mul_squarefree`), the scaling reduction shows that to prove the
conjecture for *all* `n` it suffices to prove it for all *squarefree* `n`. -/
theorem A271510.witnessSpec_of_squarefree
    (H : ∀ a : ℕ, Squarefree a → A271510.WitnessSpec a) (n : ℕ) :
    A271510.WitnessSpec n := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact ⟨0, 0, 0, 0, by ring, le_refl 0, 0, by ring⟩
  · obtain ⟨a, b, hab, hsf⟩ := Nat.sq_mul_squarefree n
    have : A271510.WitnessSpec (b ^ 2 * a) := A271510.witnessSpec_scale b a (H a hsf)
    rwa [hab] at this

/-- **Family I.**  If `n` is a sum of two squares, `n = a² + b²`, then it admits a
witness with `y = z = 0` (the constraint `x² = a²` is then automatically a square).
This proves the conjecture for every sum of two squares. -/
theorem A271510.witnessSpec_sq_add_sq (a b : ℕ) :
    A271510.WitnessSpec (a ^ 2 + b ^ 2) :=
  ⟨a, 0, 0, b, by ring, Nat.zero_le a, a, by ring⟩

/-- **Family II.**  Every `n = 2a² + b²` admits a witness `(a, a, 0, b)`: the
constraint is `a² + 8a² = 9a² = (3a)²`. -/
theorem A271510.witnessSpec_two_mul_sq_add_sq (a b : ℕ) :
    A271510.WitnessSpec (2 * a ^ 2 + b ^ 2) :=
  ⟨a, a, 0, b, by ring, le_refl a, 3 * a, by ring⟩

/-- **Family III.**  Every `n = 3a² + b²` admits a witness `(a, a, a, b)`: the
constraint is `a² + 8a² + 16a² = 25a² = (5a)²`. -/
theorem A271510.witnessSpec_three_mul_sq_add_sq (a b : ℕ) :
    A271510.WitnessSpec (3 * a ^ 2 + b ^ 2) :=
  ⟨a, a, a, b, by ring, le_refl a, 5 * a, by ring⟩

/--
The arithmetic heart of the conjecture, isolated as a clean existence statement
on **squarefree** `n` (the scaling reduction `witnessSpec_of_squarefree` lifts this
to all `n`).  For squarefree `n` this is the genuine open kernel: it is governed by
the spinor genus of the ternary form `x²+8y²+16z²=□` together with the four–square
structure, and (by Duke–Schulze-Pillot) holds for all sufficiently large `n` — but
ineffectively.  This is Z.-W. Sun's conjecture (OEIS A271510). -/
theorem A271510.exists_witness_squarefree (n : ℕ) (hn : Squarefree n) :
    A271510.WitnessSpec n := by
  sorry

/-- The arithmetic heart for **all** `n`, obtained from the squarefree kernel via
the scaling reduction. -/
theorem A271510.exists_witness (n : ℕ) :
    ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ x ≥ y ∧
      is_square (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) :=
  A271510.witnessSpec_of_squarefree A271510.exists_witness_squarefree n

/--
Conjecture (i) existence part from OEIS A271510:
a(n) > 0 for all n = 0,1,2,...
-/
theorem oeis_A271510_conjecture_i_positive :
  ∀ n : ℕ, 0 < A271510 n
  := by
  intro n
  obtain ⟨x, y, z, w, hsum, hxy, hsq⟩ := A271510.exists_witness n
  exact A271510.witness_pos' n x y z w hsum hxy hsq
