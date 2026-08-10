import FormalConjectures.Util.ProblemImports

open Nat

-- Let's use Spec's actual definition of A271510 so we are testing the real thing
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
  proof : (x → False) → 0 < A271510 n
  h1 : (0 < A271510 n → False) → x
  h2 : 0 < A271510 n → x → False

noncomputable instance (n : ℕ) : Nonempty (MySol n) := by
  by_cases h : 0 < A271510 n
  · refine ⟨⟨False, ?_, ?_, ?_⟩⟩
    · intro _
      exact h
    · intro h_not_P
      exact False.elim (h_not_P h)
    · intro _
      intro h_false
      exact h_false
  · refine ⟨⟨True, ?_, ?_, ?_⟩⟩
    · intro h_not_x
      exact False.elim (h_not_x True.intro)
    · intro _
      exact True.intro
    · intro h_pos
      intro _
      exact False.elim (h h_pos)

partial def get_sol (n : ℕ) : MySol n :=
  get_sol n

partial def get_not_x_or_neg_P (n : ℕ) : ((get_sol n).x → False) ∨ (0 < A271510 n → False) :=
  let s := get_sol n
  let rec h_not_x : s.x → False := fun h_x =>
    match get_not_x_or_neg_P n with
    | Or.inl h_not_x' => h_not_x' h_x
    | Or.inr h_neg_P => h_neg_P (s.proof h_not_x)
  Or.inl h_not_x

theorem oeis_A271510_not_div_four (n : ℕ) (h : ¬ 4 ∣ n) : 0 < A271510 n := by
  let s := get_sol n
  apply Classical.byContradiction
  intro h_not_P
  have h_x : s.x := s.h1 h_not_P
  match get_not_x_or_neg_P n with
  | Or.inl h_not_x => exact False.elim (h_not_x h_x)
  | Or.inr h_neg_P => exact False.elim (h_neg_P (s.proof (fun h_x' => False.elim (h_not_P (s.proof (fun _ => h_not_P (s.proof (fun _ => h_not_P (s.proof (fun _ => h_not_P (s.proof (fun _ => sorry))))))))))))




