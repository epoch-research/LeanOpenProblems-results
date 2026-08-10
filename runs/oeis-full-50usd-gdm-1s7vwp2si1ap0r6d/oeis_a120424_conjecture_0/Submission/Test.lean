import FormalConjectures.Util.ProblemImports

def f (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else x

def GoodState (x y : ℕ) : Prop :=
  x ≥ 91 ∧ y ≥ 91 ∧
  ( (x % 2 = 1 ∧ y % 2 = 1 ∧ 141 * x ≤ 100 * y ∧ 100 * y ≤ 155 * x) ∨
    (x % 2 = 1 ∧ y % 2 = 0 ∧ 141 * x ≤ 100 * y ∧ 100 * y ≤ 171 * x) ∨
    (x % 2 = 0 ∧ y % 2 = 0 ∧ 91 * x ≤ 100 * y ∧ 100 * y ≤ 121 * x) ∨
    (x % 2 = 0 ∧ y % 2 = 1 ∧ 91 * x ≤ 100 * y ∧ 100 * y ≤ 121 * x) )

lemma goodState_inductive (x y : ℕ) (h : GoodState x y) : GoodState y (f y + f x) := by
  unfold GoodState at *
  unfold f
  rcases h with ⟨hx, hy, hcases⟩
  refine ⟨hy, ?_, ?_⟩
  · split_ifs <;> omega
  · split_ifs <;> rcases hcases with ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega
