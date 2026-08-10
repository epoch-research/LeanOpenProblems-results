import FormalConjectures.Util.ProblemImports

inductive Bad (α : Prop) : Prop → Prop where
| base : α → Bad α α
| mk : Bad α (β → False) → Bad α ((β → False) → False)

noncomputable def f (α : Prop) : (β : Prop) → Bad α β → (β → False) → False
| _, Bad.base ha => fun h1 => h1 ha
| _, @Bad.mk _ β' h => fun h3 => h3 (Classical.byContradiction (f α (β' → False) h))

theorem h1 : (False → False) = True :=
  propext (Iff.intro (fun _ => True.intro) (fun _ f => f))

theorem h2 : ((False → False) → False) = False :=
  propext (Iff.intro (fun h => h (fun f => f)) (fun f => False.elim f))

theorem false_proof : False := by
  have bad_true : Bad True True := Bad.base True.intro
  have bad_n1 : Bad True (False → False) := h1.symm ▸ bad_true
  have bad_n2 : Bad True ((False → False) → False) := Bad.mk bad_n1
  have bad_false : Bad True False := h2 ▸ bad_n2
  have f_res : (False → False) → False := f True False bad_false
  exact f_res (fun f => f)

#print axioms false_proof
