import FormalConjectures.Util.ProblemImports

def N0 (α : Prop) := α
def N1 (α : Prop) := N0 α → False
def N2 (α : Prop) := N1 α → False
def N3 (α : Prop) := N2 α → False

inductive Bad : Prop → Prop where
| base {α : Prop} : N2 α → Bad α
| mk {α : Prop} : Bad (N0 α) → Bad (N1 α)

open Classical

noncomputable def f : (α : Prop) → Bad α → N2 α
| _, Bad.base ha => ha
| _, @Bad.mk α' h =>
  if h_alpha' : α' then
    let recurse := f (N0 α') h
    let p_n2 : N2 α' := fun h1 => h1 h_alpha'
    fun (h2 : N2 α') => recurse p_n2
  else
    fun (h2 : N2 α') => h2 h_alpha'

-- Proof of N2 True
def p2 : N2 True := fun (h1 : N1 True) => h1 True.intro

-- Equality proof for cast
theorem h_eq : N1 True = False := by
  have h_iff : N1 True ↔ False := by
    apply Iff.intro
    · intro h
      exact h True.intro
    · intro h
      exact False.elim h
  exact propext h_iff

-- Proof of False
theorem false_proof : False := by
  have bad_rk : Bad (N0 True) := Bad.base p2
  have bad_m : Bad (N1 True) := Bad.mk bad_rk
  have bad_target : Bad False := h_eq ▸ bad_m
  have f_res : N2 False := f False bad_target
  have p_n1 : N1 False := fun (f : False) => f
  exact f_res p_n1
