import FormalConjectures.Util.ProblemImports
import Submission.ProofFinal

def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 3
  | (n + 2) => 2 * a (n + 1) + 2 * a n
termination_by n

set_option linter.unusedVariables false

theorem oeis_A028859_conjecture_1 (n : ℕ) :
  let L := n + 1
  let Sequence := Fin L → ℕ
  let S : Set Sequence :=
    { σ : Sequence |
      L > 0 ∧
      (∀ i : Fin L, σ i > 0) ∧
      let max_val := Finset.sup Finset.univ σ
      (∀ k : ℕ, 1 ≤ k ∧ k ≤ max_val → ∃ i : Fin L, σ i = k) ∧
      (∀ i j : Fin L, i < j → j.val ≠ i.val + 1 → σ i ≥ σ j)
    }
  ∃ (F : Finset Sequence), F.toSet = S ∧ F.card = a n
:= by
  exact conjecture_true n

theorem oeis_A028859_conjecture_1.disproof : ¬ (type_of% @oeis_A028859_conjecture_1) := by
  sorry
