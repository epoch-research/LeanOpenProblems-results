inductive Unsound : Prop
| mk : (Type 0 → Unsound) → Unsound
| base : (∃ (X : Type 0) (f : X → Unsound) (g : Unsound → X), (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y)) → Unsound

theorem unsound_nonempty : Unsound :=
  Unsound.base ⟨PLift Unsound, PLift.down, PLift.up, fun x => rfl, fun y => rfl⟩
