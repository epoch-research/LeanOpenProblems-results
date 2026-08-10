import FormalConjectures.Util.ProblemImports

inductive Bad (α : Prop) : Prop → Prop where
| base : α → Bad α α
| mk : Bad α ((β → False) → False) → Bad α β

noncomputable def f (α : Prop) : (β : Prop) → Bad α β → (β → False) → False
| _, Bad.base ha => fun h1 => h1 ha
| _, @Bad.mk _ β' h => Classical.byContradiction (show ¬((β' → False) → False) → False from f α ((β' → False) → False) h)

theorem h1 : (False → False) = True :=
  propext (Iff.intro (fun _ => True.intro) (fun _ f => f))

theorem h1_neg : (True → False) = False :=
  propext (Iff.intro (fun h => h True.intro) (fun f => False.elim f))

theorem h2 : ((False → False) → False) = False :=
  propext (Iff.intro (fun h => h (fun f => f)) (fun f => False.elim f))

theorem false_proof : False := by
  have bad_true : Bad True True := Bad.base True.intro
  -- True = ((False -> False) -> False)
  have h_eq : True = ((False → False) → False) := by
    have h_double_neg : True = ((True → False) → False) := by
      have h_iff : True ↔ ((True → False) → False) := by
        apply Iff.intro
        · intro _ h
          exact h True.intro
        · intro _
          exact True.intro
      exact propext h_iff
    have h_double_neg_cast : True = (((False → False) → False) → False) := by
      rw [h1.symm] at h_double_neg
      exact h_double_neg
    have h_equiv_3_2 : (((False → False) → False) → False) = ((False → False) → False) := by
      have h_iff : (((False → False) → False) → False) ↔ ((False → False) → False) := by
        apply Iff.intro
        · intro h hX
          exact h (fun hY => hY hX)
        · intro hY h_Y_not
          exact h_Y_not hY
      exact propext h_iff
    exact h_double_neg_cast.trans h_equiv_3_2
  have bad_double_neg : Bad True ((False → False) → False) := h_eq ▸ bad_true
  have bad_false : Bad True False := @Bad.mk True False bad_double_neg
  have f_res : (False → False) → False := f True False bad_false
  exact f_res (fun f => f)

#print axioms false_proof

#print axioms false_proof
