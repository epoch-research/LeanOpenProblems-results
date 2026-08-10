import FormalConjectures.Util.ProblemImports
open Nat

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

example : Target := by
  -- no empty value available
  exact nomatch (Classical.dec Target)

example : Target := by
  let h : Empty := by exact nomatch (Classical.dec False)
  exact Empty.elim h

example (P : Prop) : P := by
  let q : Quot (fun _ _ : Empty => True) := by
    -- no representative of Empty exists
    exact nomatch (Classical.dec False)
  exact nomatch Quot.out q
