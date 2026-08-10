import FormalConjectures.Util.ProblemImports

open scoped Real

noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

def C (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) : Prop :=
  ∀ (p : ℕ) (_hp : Nat.Prime p) (_h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (_hn : n > 0) (_hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))]

def r (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) (x y : Prop) : Prop :=
  (x = y) ∨ (x = True ∧ y = False ∧ (answer(sorry) : Prop))

theorem r_true_false (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  r h_int True False := Or.inr ⟨rfl, rfl, trivial⟩

theorem h_eq (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  Quot.mk (r h_int) True = Quot.mk (r h_int) False := Quot.sound (r_true_false h_int)

-- Now we define g_respects with a sorry of type Prop!
def g_respects (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  Prop := answer(sorry)

-- wait, does g_respects elaborate to True?
-- Let's check!

#print axioms h_eq
#print axioms g_respects
