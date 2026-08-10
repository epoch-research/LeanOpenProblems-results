import FormalConjectures.Util.ProblemImports

instance propLT (P : Prop) : LT P := ⟨fun _ _ => True⟩
instance propLE (P : Prop) : LE P := ⟨fun _ _ => True⟩
instance propPreorder (P : Prop) : Preorder P where
  le := fun _ _ => True
  lt := fun _ _ => True
  le_refl := by intro; trivial
  le_trans := by intro; trivial
  lt_iff_le_not_ge := by intro; simp
instance propNoMax (P : Prop) : NoMaxOrder P where
  exists_gt := by intro a; exact ⟨a, trivial⟩

#synth NoMaxOrder False
#check Infinite
-- try synth
#synth Infinite False
example : False := Infinite.nonempty False |>.some
