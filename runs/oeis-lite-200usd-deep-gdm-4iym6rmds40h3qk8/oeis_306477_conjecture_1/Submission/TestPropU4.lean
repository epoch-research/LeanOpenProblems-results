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
    -- not_U U.base is U.mk (...)
    -- so we have U.mk (...) = U.base
    -- which is impossible because they are different constructors!
    nomatch h
  | mk f =>
    -- not_U (U.mk f) is U.base
    -- so we have U.base = U.mk f
    -- which is also impossible!
    nomatch h
