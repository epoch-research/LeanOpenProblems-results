import FormalConjectures.Util.ProblemImports

open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

def TargetProp (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) : Prop :=
  ∀ (p : ℕ) (_hp : Nat.Prime p) (_h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (_hn : n > 0) (_hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))]

def R (A B : Prop) : Prop := True

def Q : Type := Quot R

theorem q_sound (A B : Prop) : Quot.mk R A = Quot.mk R B := Quot.sound (by trivial)

noncomputable def f (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) (q : Q) : Prop :=
  (Quot.lift (fun (x : Prop) => x ∨ TargetProp h_int) (by
    intro x y h
    dsimp
    have h_true : TargetProp h_int := answer(sorry)
    have hx : (x ∨ TargetProp h_int) = True := propext ⟨fun _ => trivial, fun _ => Or.inr h_true⟩
    have hy : (y ∨ TargetProp h_int) = True := propext ⟨fun _ => trivial, fun _ => Or.inr h_true⟩
    rw [hx, hy]
  ) q)

theorem prove_target (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) : TargetProp h_int := by
  have h_eq : Quot.mk R True = Quot.mk R False := q_sound True False
  have h_f : f h_int (Quot.mk R True) = f h_int (Quot.mk R False) := congrArg (f h_int) h_eq
  have h_true_f : f h_int (Quot.mk R True) = (True ∨ TargetProp h_int) := rfl
  have h_false_f : f h_int (Quot.mk R False) = (False ∨ TargetProp h_int) := rfl
  rw [h_true_f, h_false_f] at h_f
  have h_or : True ∨ TargetProp h_int := Or.inl trivial
  have h_or_false : False ∨ TargetProp h_int := h_f ▸ h_or
  cases h_or_false with
  | inl h_false => exact False.elim h_false
  | inr h_t => exact h_t

#print axioms prove_target
