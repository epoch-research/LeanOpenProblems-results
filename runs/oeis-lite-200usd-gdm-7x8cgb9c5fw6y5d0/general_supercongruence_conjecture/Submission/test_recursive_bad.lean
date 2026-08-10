import FormalConjectures.Util.ProblemImports

def N0 (α : Prop) := α
def N1 (α : Prop) := N0 α → False
def N2 (α : Prop) := N1 α → False
def N3 (α : Prop) := N2 α → False

inductive Bad : Prop → Prop where
| base {α : Prop} : N1 α → Bad α
| mk {α : Prop} : Bad (N3 α) → Bad (N1 α)

open Classical

noncomputable def f : (α : Prop) → Bad α → N1 α
| _, Bad.base ha => ha
| _, @Bad.mk α' h =>
  if h_alpha' : α' then
    fun (h1 : N1 α') => h1 h_alpha'
  else
    let recurse := f (N3 α') h
    fun (h1 : N1 α') => recurse (fun (h2 : N2 α') => h2 h1)

theorem h_n1 : N1 False = True := by
  have h_iff : N1 False ↔ True := by
    apply Iff.intro
    · intro _
      exact True.intro
    · intro _ f
      exact f
  exact propext h_iff

theorem h_n3 : N3 False = True := by
  have h_iff : N3 False ↔ True := by
    apply Iff.intro
    · intro _
      exact True.intro
    · intro _ h2 h1
      exact h2 h1
  exact propext h_iff

theorem h_eq : N3 False = N1 False := h_n3.trans h_n1.symm

-- Can we define bad_n1 recursively?
noncomputable def bad_n1 : Bad (N1 False) := Bad.mk (h_eq ▸ bad_n1)
