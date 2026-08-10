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

lemma solve_for_sum_of_two_squares (b c : ℕ) (n : ℕ) (x w : ℕ) (h : x^2 + w^2 = n) :
  ∃ x' y' z' w' : ℕ, x'^2 + y'^2 + z'^2 + w'^2 = n ∧ x' ≥ y' ∧ is_square (9*x'^2 + b*y'^2 + c*z'^2) := by
  use x, 0, 0, w
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · omega
  · use 3 * x
    ring

lemma solve_for_63_7 (n : ℕ) (a w : ℕ) (h : (1764*a^4 + 88*a^2 + 2) + w^2 = n) :
  ∃ x' y' z' w' : ℕ, x'^2 + y'^2 + z'^2 + w'^2 = n ∧ x' ≥ y' ∧ is_square (9*x'^2 + 63*y'^2 + 7*z'^2) := by
  use 42*a^2 + 1, 2*a, 1, w
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have : a^2 ≥ a := Nat.le_self_pow (by decide) a
      omega
  · use 126*a^2 + 4
    ring

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
    intro h n
    by_cases h_2sq : ∃ x w : ℕ, x^2 + w^2 = n
    · rcases h_2sq with ⟨x, w, hsq⟩
      exact solve_for_sum_of_two_squares b c n x w hsq
    · sorry
#print axioms oeis_A271510_conjecture_iii
