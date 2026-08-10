import FormalConjectures.Util.ProblemImports

inductive T : (α : Type) → ((α → Prop) → Prop) → Prop
| base : T PUnit (fun g ↦ g PUnit.unit)
| mk : {α : Type} → (a : ((α → Prop) → Prop) → Prop) → T α (fun g ↦ a (fun _ ↦ True)) → T (α → Prop) a
| cheat : T (PUnit → Prop) (fun _ ↦ False)

theorem unsound {α : Type} {a : (α → Prop) → Prop} (t : T α a) : a (fun _ ↦ True) := by
  induction t with
  | base => exact True.intro
  | mk a' t_1 ih => exact ih
  | cheat => contradiction

theorem unsound_proof_of_false : False := by
  have t : T (PUnit → Prop) (fun _ ↦ False) := T.cheat
  exact unsound t
