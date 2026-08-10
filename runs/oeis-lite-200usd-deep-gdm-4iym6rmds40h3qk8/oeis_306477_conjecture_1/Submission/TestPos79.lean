open Classical

inductive T : Type 1 where
  | base : T

-- Since T is in Type 1, the subtype { x : T // x = t } is also in Type 1!
-- So MyType t is of type Type 1, not Type!
-- To make it of type Type, we must use ULift or similar.
-- Wait, if we use ULift, does it still work?
-- ULift ({ x : T // x = t }) is of type Type!
-- Let's check!
def MyType (t : T) : Type := ULift ({ x : T // x = t })

theorem MyType_inj (t1 t2 : T) (h : MyType t1 = MyType t2) : t1 = t2 := by
  let val1 : MyType t1 := ULift.up ⟨t1, rfl⟩
  let val2 : MyType t2 := cast h val1
  have h_prop := val2.down.property
  exact h_prop
