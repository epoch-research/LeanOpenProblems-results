import FormalConjectures.Util.ProblemImports

def N0 (α : Prop) := α
def N1 (α : Prop) := N0 α → False
def N2 (α : Prop) := N1 α → False
def N3 (α : Prop) := N2 α → False

inductive Bad : Prop → Prop where
| base {α : Prop} : N2 α → Bad α
| mk {α : Prop} : Bad (N2 α) → Bad (N0 α)

noncomputable def f : (α : Prop) → Bad α → N2 α
| _, Bad.base ha => ha
| _, @Bad.mk α' h =>
  let recurse := f (N2 α') h
  fun (h1 : N1 α') => recurse (fun (h2 : N2 α') => h2 h1)

theorem false_proof : False := by
  have p_n1 : N1 False := fun (f : False) => f
  have p_n2 : N2 False := fun (h1 : N1 False) => h1 p_n1
  have bad_n2_false : Bad (N2 False) := Bad.base p_n2
  have bad_false : Bad False := @Bad.mk False bad_n2_false
  have f_res : N2 False := f False bad_false
  exact f_res p_n1
