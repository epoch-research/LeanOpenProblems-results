open Classical

def U : Prop := ∀ p : Prop, ((((p → Prop) → Prop) → p) → p)

noncomputable def le (x : (U → Prop) → Prop) : U :=
  fun p f => f (fun (y : p → Prop) => x (fun (u : U) => y (u p f)))

noncomputable def ge (x : U) : (U → Prop) → Prop :=
  fun h => h x

theorem le_ge (x : (U → Prop) → Prop) : ge (le x) = x := by
  ext h
  dsimp [ge]
  -- We want to prove: h (le x) ↔ x h
  sorry
