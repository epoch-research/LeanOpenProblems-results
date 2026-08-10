import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : (α : Type) → (α → Prop) → Prop
| base : T PUnit.{1} (fun _ ↦ True)
| mk : {α : Type} → (a : (α → Prop) → Prop) → T α (fun x ↦ a (fun g ↦ g x)) → T (α → Prop) a

def t_0 : T PUnit.{1} (fun _ ↦ True) := T.base

def t_1 : T (PUnit.{1} → Prop) (fun p ↦ p (fun _ ↦ True)) :=
  T.mk (fun p ↦ p (fun _ ↦ True)) t_0

def t_2 : T ((PUnit.{1} → Prop) → Prop) (fun p ↦ p (fun f ↦ f (fun _ ↦ True))) :=
  T.mk (fun p ↦ p (fun f ↦ f (fun _ ↦ True))) t_1
