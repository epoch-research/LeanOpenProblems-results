import FormalConjectures.Util.ProblemImports

inductive T : (α : Type) → (α → Prop) → Prop
| base : T PUnit (fun _ ↦ True)
| mk : {α : Type} → (a : (α → Prop) → Prop) → T α (fun _ ↦ a (fun _ ↦ True)) → T (α → Prop) a

def bad {α} {a} (t : T α a) : (∀ x : α, a x → False) → False := by
  induction t with
  | base =>
    intro h
    exact h PUnit.unit True.intro
  | mk a' t_1 ih =>
    intro h
    exact ih (fun x ↦ h (fun _ ↦ True))
