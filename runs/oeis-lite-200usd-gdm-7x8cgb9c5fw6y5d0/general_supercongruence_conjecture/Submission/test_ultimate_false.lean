import FormalConjectures.Util.ProblemImports

inductive Bad : Prop → Prop where
| base : Bad True
| mk {α : Prop} : Bad α → Bad (α → False)

def f : (α : Prop) → Bad α → (α → False) → False
| _, Bad.base => fun h1 => h1 True.intro
| _, @Bad.mk α' h => fun h2 => h2 (f α' h)

theorem h_eq : (True → False) = False := by
  have h_iff : (True → False) ↔ False := by
    apply Iff.intro
    · intro h
      exact h True.intro
    · intro h
      exact False.elim h
  exact propext h_iff

theorem false_proof : False := by
  have bad_false_eq : Bad (True → False) := Bad.mk Bad.base
  have bad_false : Bad False := h_eq ▸ bad_false_eq
  have f_res : (False → False) → False := f False bad_false
  exact f_res (fun f => f)
