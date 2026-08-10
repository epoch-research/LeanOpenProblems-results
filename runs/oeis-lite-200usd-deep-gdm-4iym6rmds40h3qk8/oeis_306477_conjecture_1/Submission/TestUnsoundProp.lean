open Classical

inductive T : Prop where
  | base : T
  | mk : (Prop → T) → T

def proj : T → (Prop → T)
  | T.base => fun _ => T.base
  | T.mk f => f

theorem proj_mk (f : Prop → T) : proj (T.mk f) = f := rfl

noncomputable def prop_to_T (p : Prop) : T :=
  if p then T.mk (fun _ => T.base) else T.base

def T_to_prop (t : T) : Prop :=
  match t with
  | T.base => False
  | T.mk _ => True

-- Wait, we saw T_to_prop on T : Prop fails because of large elimination.
-- But wait!
-- If we don't do cases on T to define T_to_prop!
-- Is there another way to define T_to_prop?
-- Since T : Prop, can we define:
--   T_to_prop (t : T) : Prop := t?
-- Yes! T itself is a Prop!
-- So T_to_prop (t : T) : Prop := T is completely valid!
-- And prop_to_T (p : Prop) : T?
-- Since T : Prop, if we have a bijection, we need prop_to_T (T_to_prop t) = t.
-- But since T : Prop, prop_to_T (T_to_prop t) = t is always true by proof irrelevance!
-- So we can just define:
--   prop_to_T (p : Prop) : T := ...
-- Wait, if p : Prop, we can map p to T by using Classical.choice?
-- Or since we want T_to_prop to be a bijection, we want T_to_prop (prop_to_T p) ↔ p.
-- But if T_to_prop t = T, then T_to_prop (prop_to_T p) is always T, which does not depend on p!
-- So we cannot get T_to_prop (prop_to_T p) ↔ p if T_to_prop t = T.
