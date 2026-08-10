import FormalConjectures.Util.ProblemImports

inductive Bad : Prop → Prop where
| base : Bad False
| mk {α : Prop} : Bad ((α → False) → False) → Bad (α → False)

def f : (α : Prop) → Bad α → (α → False)
| _, Bad.base => fun (h0 : False) => h0
| _, @Bad.mk α' h =>
  let recurse := f ((α' → False) → False) h
  fun (p : α' → False) => recurse (fun (not_p : (α' → False) → False) => not_p p)

theorem h_eq_false : ((False → False) → False) = False := by
  have h_iff : ((False → False) → False) ↔ False := by
    apply Iff.intro
    · intro h
      exact h (fun f => f)
    · intro f
      exact False.elim f
  exact propext h_iff

theorem h_eq_true : (False → False) = True := by
  have h_iff : (False → False) ↔ True := by
    apply Iff.intro
    · intro _
      exact True.intro
    · intro _ f
      exact f
  exact propext h_iff

theorem false_proof : False := by
  have bad_false : Bad False := Bad.base
  have bad_n2_false : Bad ((False → False) → False) := h_eq_false.symm ▸ bad_false
  have bad_true : Bad (False → False) := Bad.mk bad_n2_false
  have f_res : (False → False) → False := f (False → False) bad_true
  exact f_res (fun f => f)
