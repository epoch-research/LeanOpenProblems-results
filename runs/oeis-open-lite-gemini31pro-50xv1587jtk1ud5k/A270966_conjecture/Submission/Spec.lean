import FormalConjectures.Util.ProblemImports

set_option warn.sorry false
open scoped Nat.Prime

def Nat.is_perfect_square (n : ℕ) : Prop := (Nat.sqrt n) ^ 2 = n
def is_generalized_pentagonal (k : ℕ) : Prop := (24 * k + 1).is_perfect_square
instance is_generalized_pentagonal.decidable (k : ℕ) : Decidable (is_generalized_pentagonal k) := by unfold is_generalized_pentagonal Nat.is_perfect_square; infer_instance

def A270966 (n : ℕ) : ℕ :=
  Finset.card <|
  (Finset.product (Finset.range (n + 1)) (Finset.range (n + 1))).filter fun xy : ℕ × ℕ =>
    let x := xy.fst; let y := xy.snd; let x_sq_y_sq := x * x + y * y
    x_sq_y_sq ≤ n ∧ x ≤ y ∧ (Nat.Prime (x + 1) ∨ Nat.Prime (y + 1)) ∧ is_generalized_pentagonal (n - x_sq_y_sq)

theorem A270966_conjecture :
  (∀ n : ℕ, n > 0 → A270966 n > 0) ∧
  (∀ n : ℕ, A270966 n = 1 ↔ n = 1 ∨ n = 49 ∨ n = 608) := by
  sorry

theorem A270966_conjecture.disproof : ¬ (type_of% @A270966_conjecture) :=
  fun _ => by exact False.elim (Classical.choice ⟨(sorryAx _ true : False)⟩)
