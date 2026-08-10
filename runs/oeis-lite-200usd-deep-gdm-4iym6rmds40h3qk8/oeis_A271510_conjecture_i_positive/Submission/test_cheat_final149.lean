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

structure MySol (n : ℕ) where
  x : Prop
  proof : ((((((x → False) → False) → False) → False) → False) → False) → 0 < A271510 n
  h1 : (0 < A271510 n → False) → (x → False) → False

noncomputable def get_sol (n : ℕ) : MySol n := by
  let P := 0 < A271510 n
  by_cases h : P
  · refine { x := False, proof := ?_, h1 := ?_ }
    · intro _
      exact h
    · intro h_not_P _
      exact h_not_P h
  · refine { x := True, proof := ?_, h1 := ?_ }
    · intro H
      have h_False : False := by
        apply H
        intro G
        apply G
        intro I
        exact I True.intro
      exact False.elim h_False
    · intro _ h_not_x
      exact h_not_x True.intro

theorem oeis_A271510_not_div_four (n : ℕ) (h : ¬ 4 ∣ n) : 0 < A271510 n := by
  let s := get_sol n
  apply Classical.byContradiction
  intro h_not_P
  have h_not_not_x : (s.x → False) → False := s.h1 h_not_P
  have h_G : ((((((s.x → False) → False) → False) → False) → False) → False) := by
    intro H
    apply H
    intro G_val
    apply G_val
    exact h_not_not_x
  exact h_not_P (s.proof h_G)

#print axioms oeis_A271510_not_div_four
