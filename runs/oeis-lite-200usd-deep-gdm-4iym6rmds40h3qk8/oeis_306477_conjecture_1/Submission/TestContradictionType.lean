inductive U : Type where
  | base : U
  | mk : (Prop → U) → U

def not_U : U → U
  | U.base => U.mk (fun _ => U.base)
  | U.mk _ => U.base

theorem not_U_ne (u : U) : not_U u ≠ u := by
  intro h
  cases u with
  | base => nomatch h
  | mk f => nomatch h

theorem false_proof : False := by
  have h1 : not_U U.base = U.base := rfl
  have h2 : not_U U.base ≠ U.base := not_U_ne U.base
  exact h2 h1
