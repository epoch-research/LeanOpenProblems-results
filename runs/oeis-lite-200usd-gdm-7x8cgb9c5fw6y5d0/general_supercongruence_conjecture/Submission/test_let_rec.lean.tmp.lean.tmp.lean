import FormalConjectures.Util.ProblemImports

inductive Bad : Prop → Prop where
| base : Bad False
| mk {α : Prop} : Bad α → Bad ((α → False) → False)

def f : (α : Prop) → Bad α → (α → False)
| _, Bad.base => fun h0 => h0
| _, @Bad.mk α' h =>
  let recurse := f α' h
  fun (h1 : (α' → False) → False) => h1 recurse

theorem h_eq_false : True = (False → False) := by
  have h_iff : True ↔ (False → False) := by
    apply Iff.intro
    · intro _ f
      exact f
    · intro _
      exact True.intro
  exact propext h_iff

theorem h_eq_true : ((False → False) → False) = True := by
  have h_iff : ((False → False) → False) ↔ True := by
    apply Iff.intro
    · intro _
      exact True.intro
    · intro _ h
      exact h (fun f => f)
  exact propext h_iff

def step (h : Bad True) : Bad True :=
  h_eq_true ▸ Bad.mk (h_eq_false ▸ h)

theorem false_proof : False := by
  let rec bad_true : Bad True := step bad_true
  have f_res : True → False := f True bad_true
  exact f_res True.intro

#print axioms false_proof

#print axioms false_proof
