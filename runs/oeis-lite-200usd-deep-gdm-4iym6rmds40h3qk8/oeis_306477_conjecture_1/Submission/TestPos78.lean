open Classical

inductive T : Type 1 where
  | base : T

def MyType (t : T) : Type := { x : T // x = t }

theorem MyType_inj (t1 t2 : T) (h : MyType t1 = MyType t2) : t1 = t2 := by
  have h1 : Subtype (fun x => x = t1) = Subtype (fun x => x = t2) := h
  -- how to get t1 = t2?
  -- An inhabitant of MyType t1 is ⟨t1, rfl⟩.
  -- Since MyType t1 = MyType t2, we can cast ⟨t1, rfl⟩ to MyType t2!
  let val1 : MyType t1 := ⟨t1, rfl⟩
  let val2 : MyType t2 := cast h val1
  exact val2.property
