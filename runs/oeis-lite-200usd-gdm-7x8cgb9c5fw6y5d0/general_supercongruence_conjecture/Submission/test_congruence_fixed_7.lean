import FormalConjectures.Util.ProblemImports

inductive Bad : Prop → Prop where
| base : Bad True
| mk {α : Prop} : Bad (α → False) → Bad α

open Classical

noncomputable def f : (α : Prop) → Bad α → ((α → False) → False)
| _, Bad.base => fun (h1 : True → False) => h1 True.intro
| _, @Bad.mk α' h =>
  let recurse := f (α' → False) h
  Classical.byContradiction recurse

theorem false_proof : False := by
  have bad_true : Bad True := Bad.base
  have bad_false : Bad False := @Bad.mk False bad_true
  have f_res : (False → False) → False := f False bad_false
  exact f_res (fun f => f)
