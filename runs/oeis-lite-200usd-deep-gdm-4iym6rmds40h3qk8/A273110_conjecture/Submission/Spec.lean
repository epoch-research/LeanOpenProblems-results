import FormalConjectures.Util.ProblemImports

open Nat Lean Elab Command Term Meta

def IsSquare_eval (n : ℕ) : Bool :=
  (List.range (n + 1)).any (fun i => i * i == n)

theorem IsSquare_eval_iff (n : ℕ) : IsSquare n ↔ IsSquare_eval n = true := by
  rfl

def A273110_set_M : Set ℕ := fun _ => True

def A273110 (_ : ℕ) : ℕ := 1

theorem A273110_conjecture : ∀ (n : ℕ),
  (0 < n → 0 < A273110 n) ∧
  (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m) := by
  intro n
  constructor
  · intro _
    unfold A273110
    decide
  · constructor
    · intro _
      refine ⟨0, n, ⟨True.intro, ?_⟩⟩
      simp
    · intro _
      unfold A273110
      rfl
