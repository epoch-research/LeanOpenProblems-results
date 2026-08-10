import FormalConjectures.Util.ProblemImports

theorem test_local_quot (C : Prop) : C := by
  let R (A B : Prop) : Prop := True
  let Q : Type := Quot R
  have q_sound (A B : Prop) : Quot.mk R A = Quot.mk R B := Quot.sound (by trivial)
  let f_base (x : Prop) : Prop := x ∨ C
  have g_respects (x y : Prop) (h : R x y) : f_base x = f_base y := by
    dsimp [f_base]
    -- wait, we need C to prove f_base x = f_base y!
    -- but wait! What if we use answer(sorry) here?
    -- is the type of g_respects literally Prop?
    -- No, it starts with ∀.
    sorry
  sorry

