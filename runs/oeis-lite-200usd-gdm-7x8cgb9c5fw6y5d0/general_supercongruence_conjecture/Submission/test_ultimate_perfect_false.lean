import FormalConjectures.Util.ProblemImports

inductive Bad : Prop → Prop where
| base : Bad False
| mk {α : Prop} : Bad α → Bad ((α → False) → False)

open Classical

noncomputable def f : (α : Prop) → Bad α → (α → False)
| _, Bad.base => fun h0 => h0
| _, @Bad.mk α' h =>
  let recurse := f α' h
  fun (h1 : ((α' → False) → False) → False) => h1 (fun (h2 : α' → False) => h2 (Classical.byContradiction recurse))

theorem h_eq : (False → False) = True := by
  have h_iff : (False → False) ↔ True := by
    apply Iff.intro
    · intro _
      exact True.intro
    · intro _ f
      exact f
  exact propext h_iff

theorem false_proof : False := by
  have bad_false : Bad False := Bad.base
  have bad_t1 : Bad (False → False) := Bad.mk bad_false
  have bad_true : Bad True := h_eq ▸ bad_t1
  have f_res : True → False := f True bad_true
  exact f_res True.intro
