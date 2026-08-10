import FormalConjectures.Util.ProblemImports

universe u
abbrev QType := Quot (fun _ _ : Type => True)
def qt (α : Type) : QType := Quot.mk _ α

inductive HasElem : QType → Prop where
| intro {α : Type} : α → HasElem (qt α)

example : HasElem (qt Empty) := by
  have h : qt Unit = qt Empty := Quot.sound trivial
  exact Eq.mp (congrArg HasElem h) (HasElem.intro ())

example (h : HasElem (qt Empty)) : False := by
  cases h with
  | intro a => exact nomatch a

theorem bad : False := by
  have h : qt Unit = qt Empty := Quot.sound trivial
  have he : HasElem (qt Empty) := Eq.mp (congrArg HasElem h) (HasElem.intro ())
  cases he with
  | intro a => exact nomatch a

#print axioms bad
