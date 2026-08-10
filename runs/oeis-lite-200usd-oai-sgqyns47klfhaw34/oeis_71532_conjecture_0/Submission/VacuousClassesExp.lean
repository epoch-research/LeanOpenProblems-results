import FormalConjectures.Util.ProblemImports

-- Try deriving False from vacuous order classes on Empty/False-like types
instance emptyLT : LT Empty := ⟨fun _ _ => False⟩
instance emptyLE : LE Empty := ⟨fun _ _ => True⟩
instance emptyPreorder : Preorder Empty where
  le := fun _ _ => True
  lt := fun _ _ => False
  le_refl := by intro x; cases x
  le_trans := by intro a; cases a
  lt_iff_le_not_ge := by intro a; cases a
instance emptyNoMax : NoMaxOrder Empty where
  exists_gt := by intro a; cases a
instance emptyNoMin : NoMinOrder Empty where
  exists_lt := by intro a; cases a
instance emptyWFlt : WellFoundedLT Empty where
  wf := by exact ⟨fun a => by cases a⟩
instance emptyWFgt : WellFoundedGT Empty where
  wf := by exact ⟨fun a => by cases a⟩

-- obvious no synth Infinite because needs Nonempty
#synth NoMaxOrder Empty
#synth WellFoundedLT Empty

-- Try known theorem with f : Empty -> Empty? range over Nat? no strictmono impossible domain Nat.
example : False := by
  have h := @StrictMono.not_bddAbove_range_of_wellFoundedLT Empty Empty _ _ _ _ (fun x => x)
  -- inspect h
  guard_target = False
  sorry
