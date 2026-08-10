import FormalConjectures.Util.ProblemImports

inductive T : (α : Type 0) → ((α → Prop) → Prop) → Prop
| base : T PUnit (fun g ↦ False)
| mk : {α : Type 0} → (a : ((α → Prop) → Prop) → Prop) → T α (fun g ↦ a (fun _ ↦ True)) → T (α → Prop) a

def bad_direct {α : Type 0} {a} (t : T α a) (h_eq : α = (PUnit → Prop)) : False := by
  cases t with
  | base =>
    have h_sub : Subsingleton (PUnit → Prop) := h_eq ▸ (by infer_instance : Subsingleton PUnit)
    have h_eq2 : True = False := Subsingleton.elim True False
    exact h_eq2.mp True.intro
  | mk a' t_1 =>
    cases h_eq
    -- Here t_1 : T PUnit (fun g ↦ a' (fun _ ↦ True))
    cases t_1
    -- wait, what happens here?
