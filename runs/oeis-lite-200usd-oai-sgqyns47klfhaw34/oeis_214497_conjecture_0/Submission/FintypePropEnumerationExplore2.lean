import FormalConjectures.Util.ProblemImports
open Nat
abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

#check (Fintype.elems : Finset Prop)
#eval ((Fintype.elems : Finset Prop).toList.map (fun P => decide P))
example : Target ∈ (Fintype.elems : Finset Prop) := Fintype.complete Target
example : Target ∈ ({True, False} : Finset Prop) := by
  simpa using (Fintype.complete Target : Target ∈ (Fintype.elems : Finset Prop))

example : Target := by
  have hm : Target ∈ ({True, False} : Finset Prop) := by
    simpa using (Fintype.complete Target : Target ∈ (Fintype.elems : Finset Prop))
  simp at hm
  rcases hm with h | h
  · simpa [h]
  · -- here h : Target = False
    fail_if_success simpa [h]
    admit
