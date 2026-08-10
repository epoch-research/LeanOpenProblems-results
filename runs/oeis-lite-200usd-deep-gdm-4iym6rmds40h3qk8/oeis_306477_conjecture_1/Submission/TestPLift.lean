open Classical

inductive T : Type 1 where
  | base : T
  | mk : (Type → T) → T

def proj : T → (Type → T)
  | T.base => fun _ => T.base
  | T.mk f => f

noncomputable def inj_T (f : T → T) : T :=
  T.mk (fun X =>
    if h : X = PLift T then
      -- X is PLift T. We want to apply f to something.
      -- Since X = PLift T, we can cast a term of PLift T to X.
      -- But we are not given any term of X.
      -- Wait, if we are given x : X, we can't do it because inj_T takes f, not x.
      -- But wait!
      -- We want proj_T : T → (T → T).
      -- How is proj_T defined?
      -- proj_T t (x : T) : T := proj t (PLift T) (PLift.up x)
      T.base
  )
