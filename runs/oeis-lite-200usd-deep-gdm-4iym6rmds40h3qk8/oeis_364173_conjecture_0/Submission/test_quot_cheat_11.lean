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

def R (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) (b1 b2 : Bool) : Prop :=
  b1 = b2 ∨ (b1 = true ∧ b2 = false ∧ TargetProp h_int)

def f_base (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) (b : Bool) : Prop :=
  b = true → TargetProp h_int

theorem g_respects (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) (b1 b2 : Bool) (h : R h_int b1 b2) :
  f_base h_int b1 = f_base h_int b2 := by
  cases h with
  | inl h_eq => rw [h_eq]
  | inr h_and =>
    rcases h_and with ⟨rfl, rfl, h_target⟩
    unfold f_base
    apply propext
    constructor
    · intro _ h_false
      contradiction
    · intro _ _
      exact h_target

#print axioms g_respects
