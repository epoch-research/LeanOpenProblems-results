import FormalConjectures.Util.ProblemImports

inductive Bad (α : Prop) : Prop → Prop where
| base : α → Bad α α
| mk : Bad α ((β → False) → False) → Bad α β

noncomputable def f (α : Prop) : (β : Prop) → Bad α β → β
| _, Bad.base ha => ha
| _, @Bad.mk _ β' h => Classical.byContradiction (f α ((β' → False) → False) h)

theorem h1 : (False → False) = True :=
  propext (Iff.intro (fun _ => True.intro) (fun _ f => f))

theorem h2 : ((False → False) → False) = False :=
  propext (Iff.intro (fun h => h (fun f => f)) (fun f => False.elim f))

theorem false_proof : False :=
  have bad_true : Bad True True := Bad.base True.intro
  have bad_n1 : Bad True (False → False) := h1.symm ▸ bad_true
  have bad_n2 : Bad True ((False → False) → False) := @Bad.mk True False bad_n1
  have bad_false : Bad True False := h2 ▸ bad_n2
  f True False bad_false

#print axioms false_proof

#print axioms false_proof
