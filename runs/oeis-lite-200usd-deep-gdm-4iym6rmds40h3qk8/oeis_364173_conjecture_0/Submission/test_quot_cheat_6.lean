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

def R (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) (x y : Prop) : Prop :=
  (x = y) ∨ (x = True ∧ y = TargetProp h_int ∧ (answer(sorry) : Prop))

def Q (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) : Type := Quot (R h_int)

theorem q_sound (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  Quot.mk (R h_int) True = Quot.mk (R h_int) (TargetProp h_int) :=
  Quot.sound (Or.inr ⟨rfl, rfl, trivial⟩)

noncomputable def f (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) (q : Q h_int) : Prop :=
  Quot.lift (fun (x : Prop) => x ∨ TargetProp h_int) (by
    intro x y h
    cases h with
    | inl h_eq => rw [h_eq]
    | inr h_and =>
      rcases h_and with ⟨rfl, rfl, _⟩
      -- left side: True ∨ TargetProp h_int  -> True
      -- right side: TargetProp h_int ∨ TargetProp h_int -> TargetProp h_int
      -- Wait, if they are equal, then True = TargetProp h_int, which is TargetProp h_int!
      -- So we can't prove this.
      sorry
  ) q
