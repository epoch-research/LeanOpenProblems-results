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

private lemma A271510_le_sqrt_of_square_sum_eq {n x y z w : ℕ}
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) :
    x ≤ n.sqrt ∧ y ≤ n.sqrt ∧ z ≤ n.sqrt ∧ w ≤ n.sqrt := by
  have hx2 : x ^ 2 ≤ n := by nlinarith [hsum]
  have hy2 : y ^ 2 ≤ n := by nlinarith [hsum]
  have hz2 : z ^ 2 ≤ n := by nlinarith [hsum]
  have hw2 : w ^ 2 ≤ n := by nlinarith [hsum]
  constructor
  · exact Nat.le_sqrt.mpr (by simpa [pow_two] using hx2)
  constructor
  · exact Nat.le_sqrt.mpr (by simpa [pow_two] using hy2)
  constructor
  · exact Nat.le_sqrt.mpr (by simpa [pow_two] using hz2)
  · exact Nat.le_sqrt.mpr (by simpa [pow_two] using hw2)

private lemma A271510_pos_of_witness {n x y z w : ℕ}
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n)
    (hxy : x ≥ y)
    (hsq : (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt *
        (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt =
      x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) : 0 < A271510 n := by
  rw [A271510]
  dsimp only
  apply Finset.card_pos.mpr
  let p : (((ℕ × ℕ) × ℕ) × ℕ) := (((x, y), z), w)
  refine ⟨p, ?_⟩
  have hb := A271510_le_sqrt_of_square_sum_eq hsum
  simp only [Finset.mem_filter]
  constructor
  · simp [p, Finset.mem_product]
    exact ⟨⟨⟨hb.1, hb.2.1⟩, hb.2.2.1⟩, hb.2.2.2⟩
  · exact ⟨hsum, hxy, hsq⟩


/--
Conjecture (i) existence part from OEIS A271510:
a(n) > 0 for all n = 0,1,2,...
-/
theorem oeis_A271510_conjecture_i_positive :
  ∀ n : ℕ, 0 < A271510 n := by
  intro n
  sorry
