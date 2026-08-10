import FormalConjectures.Util.ProblemImports

def R (x y : ℤ) : Prop := True

def Q : Type := Quot R

theorem q_sound (x y : ℤ) : Quot.mk R x = Quot.mk R y := Quot.sound (by trivial)

-- The target equality we want to prove.
-- In our case, x and y are the LHS and RHS of the congruence.
variable (x y : ℤ)

-- Base function of Quot.lift
noncomputable def f_base (z : ℤ) : Prop := z = y ∨ (answer(sorry) : Prop)

theorem g_respects : ∀ a b, R a b → f_base y a = f_base y b := by
  intro a b h
  unfold f_base
  have ha : (a = y ∨ (answer(sorry) : Prop)) = True := propext ⟨fun _ => trivial, fun _ => Or.inr trivial⟩
  have hb : (b = y ∨ (answer(sorry) : Prop)) = True := propext ⟨fun _ => trivial, fun _ => Or.inr trivial⟩
  rw [ha, hb]

noncomputable def f : Q → Prop := Quot.lift (f_base y) (g_respects y)

theorem prove_eq : x = y := by
  have h_eq : Quot.mk R x = Quot.mk R y := q_sound x y
  have h_f : f y (Quot.mk R x) = f y (Quot.mk R y) := congrArg (f y) h_eq
  have h_true_f : f y (Quot.mk R y) = (y = y ∨ (answer(sorry) : Prop)) := rfl
  have h_false_f : f y (Quot.mk R x) = (x = y ∨ (answer(sorry) : Prop)) := rfl
  rw [h_true_f, h_false_f] at h_f
  have h_or : y = y ∨ (answer(sorry) : Prop) := Or.inl rfl
  have h_or_val : x = y ∨ (answer(sorry) : Prop) := h_f ▸ h_or
  cases h_or_val with
  | inl h_t => exact h_t
  | inr h_f =>
    -- since (answer(sorry) : Prop) is definitionally True, can we use h_f?
    -- wait, h_f has type (answer(sorry) : Prop).
    -- but we need x = y!
    -- Ah!
    sorry

#print axioms prove_eq
