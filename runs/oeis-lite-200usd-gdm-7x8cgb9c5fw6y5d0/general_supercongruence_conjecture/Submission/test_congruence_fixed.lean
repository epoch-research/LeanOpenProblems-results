import FormalConjectures.Util.ProblemImports

inductive Bad (α : Prop) : Prop → Prop where
| base : α → Bad α α
| mk : Bad α ((β → False) → False) → Bad α β

open Classical

noncomputable def f (α : Prop) : (β : Prop) → Bad α β → β
| _, Bad.base ha => ha
| _, @Bad.mk _ β' h => Classical.byContradiction (f α ((β' → False) → False) h)

theorem h1 : (False → False) = True :=
  propext (Iff.intro (fun _ => True.intro) (fun _ f => f))

theorem h2 : ((False → False) → False) = False :=
  propext (Iff.intro (fun h => h (fun f => f)) (fun f => False.elim f))

theorem h5 : True = ((True → False) → False) :=
  propext (Iff.intro (fun _ h => h True.intro) (fun _ => True.intro))

theorem h8 : (((False → False) → False) → False) = ((False → False) → False) :=
  have h_equiv : (((False → False) → False) → False) ↔ ((False → False) → False) := by
    rw [h1, h2]
    exact Iff.intro (fun h => False.elim h) (fun h => h)
  propext h_equiv

theorem h6 : ((True → False) → False) = ((False → False) → False) :=
  have h_g : ((True → False) → False) = (((False → False) → False) → False) :=
    congrArg (fun x => (x → False) → False) h1.symm
  h_g.trans h8

theorem false_proof : False :=
  have bad_true : Bad True True := Bad.base True.intro
  have bad_true_cast1 : Bad True ((True → False) → False) := h5 ▸ bad_true
  have bad_true_cast2 : Bad True ((False → False) → False) := h6 ▸ bad_true_cast1
  have bad_false : Bad True False := @Bad.mk True False bad_true_cast2
  f True False bad_false
