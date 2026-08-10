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

/-- The representability predicate appearing in the conjecture. -/
def Good (b c n : ℕ) : Prop :=
  ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧ x ≥ y ∧
    is_square (9 * x ^ 2 + b * y ^ 2 + c * z ^ 2)

/-- Every sum of two squares is representable: take `(max a d, 0, 0, min a d)`; then the
auxiliary value is `9·x² = (3x)²`, a square. Fully rigorous. -/
lemma good_two_sq (b c a d : ℕ) : Good b c (a ^ 2 + d ^ 2) := by
  rcases le_total d a with h | h
  · exact ⟨a, 0, 0, d, by ring, Nat.zero_le _, 3 * a, by ring⟩
  · exact ⟨d, 0, 0, a, by ring, Nat.zero_le _, 3 * d, by ring⟩

/-- **Scaling reduction.** The condition `9x² + by² + cz² = m²` is homogeneous of
degree 2, so multiplying a representation of `s` componentwise by `k` yields a
representation of `s * k²` (the auxiliary value scales by `k²`, staying a square).
This is fully rigorous. -/
lemma good_scale {b c s : ℕ} (k : ℕ) (h : Good b c s) : Good b c (s * k ^ 2) := by
  obtain ⟨x, y, z, w, hsum, hxy, m, hm⟩ := h
  refine ⟨k * x, k * y, k * z, k * w, ?_, ?_, k * m, ?_⟩
  · have : (k * x) ^ 2 + (k * y) ^ 2 + (k * z) ^ 2 + (k * w) ^ 2
        = k ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by ring
    rw [this, hsum]; ring
  · exact Nat.mul_le_mul (le_refl k) hxy
  · have : 9 * (k * x) ^ 2 + b * (k * y) ^ 2 + c * (k * z) ^ 2
        = k ^ 2 * (9 * x ^ 2 + b * y ^ 2 + c * z ^ 2) := by ring
    rw [this, hm]; ring

/-- **Reduction to the squarefree case.** Writing `n = k² * a` with `a` squarefree
(`Nat.sq_mul_squarefree`) and applying `good_scale`, the full conjecture follows from
its restriction to squarefree `n`. This is fully rigorous. -/
lemma reduce_to_squarefree {b c : ℕ}
    (hcore : ∀ a : ℕ, Squarefree a → Good b c a) : ∀ n : ℕ, Good b c n := by
  intro n
  obtain ⟨a, k, hak, ha⟩ := Nat.sq_mul_squarefree n
  have : Good b c (a * k ^ 2) := good_scale k (hcore a ha)
  rwa [mul_comm, hak] at this

/--
Conjecture (iii) from OEIS A271510:
For any ordered pair (b, c) = (48, 112), (63, 7), (112, 1008), (136, 24), (136, 216), (360, 40), (840, 280), (1008, 112), each natural number can be written as x^2 + y^2 + z^2 + w^2 with x >= y >= 0, z >=0 and w >= 0 such that 9*x^2 + b*y^2 + c*z^2 is a square.
-/
theorem oeis_A271510_conjecture_iii (b c : ℕ) :
  (b = 48 ∧ c = 112) ∨
  (b = 63 ∧ c = 7) ∨
  (b = 112 ∧ c = 1008) ∨
  (b = 136 ∧ c = 24) ∨
  (b = 136 ∧ c = 216) ∨
  (b = 360 ∧ c = 40) ∨
  (b = 840 ∧ c = 280) ∨
  (b = 1008 ∧ c = 112) →
  ∀ n : ℕ, ∃ x y z w : ℕ,
    x^2 + y^2 + z^2 + w^2 = n ∧
    x ≥ y ∧
    is_square (9*x^2 + b*y^2 + c*z^2)
  := by
  intro _ n
  -- By `reduce_to_squarefree` it suffices to treat squarefree `n`.  For such `n` that
  -- happen to be sums of two squares we are done by `good_two_sq`.  The remaining case
  -- (squarefree, not a sum of two squares) is the genuinely open analytic content of
  -- Sun's conjecture (it requires the distribution of the constrained representation
  -- count `r(n)`, governed by weight-3/2 theta series of the ternary forms
  -- `9x²+by²+cz²`, whose determinants (3969, …, 2116800) give multiple classes per
  -- genus, so cusp forms — not elementary/regular-form arguments — are required).
  refine reduce_to_squarefree (fun a _ => ?_) n
  by_cases h : ∃ p q : ℕ, a = p ^ 2 + q ^ 2
  · obtain ⟨p, q, rfl⟩ := h
    exact good_two_sq _ _ p q
  · sorry
