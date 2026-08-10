import FormalConjectures.Util.ProblemImports

inductive Flag (P : Prop) : Prop where
| mk : (b : Bool) → (b = true → P) → Flag P

instance (P : Prop) : Nonempty (Flag P) := ⟨Flag.mk false (by intro h; cases h)⟩

partial def flagTrue (P : Prop) : Flag P :=
  Flag.mk true (fun _ => by
    -- try to extract recursively
    have h := flagTrue P
    cases h with
    | mk b cert =>
      cases b
      · exact False.elim (by contradiction)
      · exact cert rfl)

#print flagTrue
#print axioms flagTrue

theorem extractFlag (P : Prop) (h : Flag P) : P := by
  cases h with
  | mk b cert =>
    cases b
    · -- impossible? no
      exact False.elim (by contradiction)
    · exact cert rfl

#print axioms extractFlag

example (P : Prop) : P := extractFlag P (flagTrue P)
#print axioms _example
