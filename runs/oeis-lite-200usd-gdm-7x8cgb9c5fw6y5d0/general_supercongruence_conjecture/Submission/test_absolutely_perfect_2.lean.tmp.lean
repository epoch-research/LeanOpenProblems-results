import FormalConjectures.Util.ProblemImports

inductive Bad : Prop → Prop where
| base {α : Prop} : ((α → False) → False) → Bad α
| mk {α : Prop} : Bad ((α → False) → False) → Bad α

def f : (α : Prop) → Bad α → (α → False) → False
| _, Bad.base ha => ha
| _, @Bad.mk α' h =>
  let recurse := f ((α' → False) → False) h
  fun (h1 : α' → False) => recurse (fun (h3 : (α' → False) → False) => h3 h1)

theorem false_proof : False := by
  have p_n2 : ((False → False) → False) := fun (h1 : False → False) =>
    h1 (fun (f : False) => f)
  have bad_false : Bad False := Bad.base p_n2
  have f_res : (False → False) → False := f False bad_false
  exact f_res (fun (f : False) => f)

#print axioms false_proof
