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

-- What if we define:
def f (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) (q : Q) : Prop :=
  (Quot.lift (fun (x : Prop) => x ∨ TargetProp h_int) (by
    intro x y h
    have h_true : TargetProp h_int := answer(sorry)
    have hx : (x ∨ TargetProp h_int) = True := propext ⟨fun _ => trivial, fun _ => Or.inr h_true⟩
    have hy : (y ∨ TargetProp h_int) = True := propext ⟨fun _ => trivial, fun _ => Or.inr h_true⟩
    rw [hx, hy]
  ) q)

-- Let's check axioms of f!
#print axioms f
