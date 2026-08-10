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

-- What if we define a helper theorem:
theorem h_target_is_true (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  TargetProp h_int := answer(sorry)

theorem g_respects (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) (x y : Prop) (h : R x y) :
  (x ∨ TargetProp h_int) = (y ∨ TargetProp h_int) := by
  have h_true : TargetProp h_int := h_target_is_true h_int
  have hx : (x ∨ TargetProp h_int) = True := propext ⟨fun _ => trivial, fun _ => Or.inr h_true⟩
  have hy : (y ∨ TargetProp h_int) = True := propext ⟨fun _ => trivial, fun _ => Or.inr h_true⟩
  rw [hx, hy]

#print axioms g_respects
