import FormalConjectures.Util.ProblemImports
open Nat
abbrev Target214497 : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

example : Target214497 ∨ ¬ Target214497 := by
  classical exact em Target214497

example : (Target214497 = True) ∨ (Target214497 = False) := Classical.propComplete Target214497

-- Both branches settle, but the disjunction itself cannot choose a declaration branch constructively.
example : Target214497 ∨ ¬ Target214497 := by
  rcases Classical.propComplete Target214497 with h | h
  · left; simpa [h]
  · right; intro ht; have : True = False := by simpa [h] using congrArg id h; exact true_ne_false this

example : Target214497 := by
  rcases Classical.propComplete Target214497 with h | h
  · simpa [h]
  · -- impossible only if we already know not false branch
    fail_if_success exact False.elim (true_ne_false (by simpa [h] : True = False))
    admit
