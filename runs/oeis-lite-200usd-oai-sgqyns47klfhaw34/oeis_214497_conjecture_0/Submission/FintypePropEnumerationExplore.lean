import FormalConjectures.Util.ProblemImports
open Nat
abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

#check Fintype.elems Prop
#eval (Fintype.elems Prop).toList.map (fun P => decide P)
#check Finset.mem_univ Target
#check Fintype.complete Target

example : Target ∈ (Fintype.elems Prop) := by exact Fintype.complete Target

example : Target := by
  have hm : Target ∈ (Fintype.elems Prop) := Fintype.complete Target
  -- membership only says it is one of the listed propositions, not that it is true
  fail_if_success simpa using hm
  admit
