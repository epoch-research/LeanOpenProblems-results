import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

def Type_of : Bool → Type 0
| true => PUnit.{1}
| false => (PUnit.{1} → Prop)

inductive T : (b : Bool) → (((Type_of b → Prop) → Prop) → Prop) → Prop
| base : T true (fun H ↦ H (fun _ ↦ True))
| mk : (a : ((Type_of false → Prop) → Prop) → Prop) → T true (fun g ↦ a (fun _ ↦ True)) → T false a

