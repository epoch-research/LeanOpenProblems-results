import FormalConjectures.Util.ProblemImports

inductive MyFlag (P : Prop) : Prop where
| mk : (b : Bool) → (b = true → P) → MyFlag P

instance (P : Prop) : Nonempty (MyFlag P) := ⟨MyFlag.mk false (by intro h; cases h)⟩

partial def myFlagTrue (P : Prop) : MyFlag P :=
  MyFlag.mk true (fun _ => by
    have h := myFlagTrue P
    cases h with
    | mk b cert =>
      cases b
      · exact False.elim (by contradiction)
      · exact cert rfl)

#print myFlagTrue
#print axioms myFlagTrue

theorem extractMyFlag (P : Prop) (h : MyFlag P) : P := by
  cases h with
  | mk b cert =>
    cases b
    · exact False.elim (by contradiction)
    · exact cert rfl

#print axioms extractMyFlag

example (P : Prop) : P := extractMyFlag P (myFlagTrue P)
#print axioms _example
