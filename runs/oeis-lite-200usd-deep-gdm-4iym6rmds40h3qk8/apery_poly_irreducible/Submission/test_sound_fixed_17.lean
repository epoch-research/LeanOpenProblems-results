import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : (α : Type) → (((α → Prop) → Prop) → Prop) → Prop
| base : T PUnit (fun H ↦ True → False)
| mk : {α : Type} → (a : (((α → Prop) → Prop) → Prop) → Prop) → T α (fun g ↦ a (fun _ ↦ True)) → T (α → Prop) a

def t_false : T (PUnit → Prop) (fun H ↦ H (fun _ ↦ True) → False) :=
  T.mk (fun H ↦ H (fun _ ↦ True) → False) T.base
