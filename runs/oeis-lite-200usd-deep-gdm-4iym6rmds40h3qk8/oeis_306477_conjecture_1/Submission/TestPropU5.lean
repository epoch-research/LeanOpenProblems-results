inductive U : Prop where
  | base : U
  | mk : (Prop → U) → U

def not_U : U → U
  | U.base => U.mk (fun _ => U.base)
  | U.mk _ => U.base

theorem not_U_ne (u : U) : not_U u ≠ u := by
  intro h
  cases u with
  | base =>
    -- not_U U.base = U.mk (fun _ => U.base)
    -- So we have U.mk (fun _ => U.base) = U.base
    -- Let's do cases h!
    cases h
  | mk f =>
    -- not_U (U.mk f) = U.base
    -- So we have U.base = U.mk f
    cases h
