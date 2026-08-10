import FormalConjectures.Util.ProblemImports

inductive T : (α : Type) → (α → Prop) → Prop
| base : T PUnit.{1} (fun _ ↦ True)
| mk : {α : Type} → (a : (α → Prop) → Prop) → T α (fun _ ↦ a (fun _ ↦ True)) → T (α → Prop) a
| cheat : T PUnit.{1} (fun _ ↦ False) → T (PUnit.{1} → Prop) (fun _ ↦ False)

def bad {α} {a : α → Prop} (t : T α a) : (∀ x : α, a x → False) → False := by
  induction t with
  | base =>
    intro h
    exact h PUnit.unit True.intro
  | mk a' t_1 ih =>
    intro h
    exact ih (fun x ↦ h (fun _ ↦ True))
  | cheat t_1 ih =>
    intro h
    exact ih (fun _ h_false ↦ h_false)
