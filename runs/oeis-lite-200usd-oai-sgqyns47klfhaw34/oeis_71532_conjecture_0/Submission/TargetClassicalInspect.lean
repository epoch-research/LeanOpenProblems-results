import FormalConjectures.Util.ProblemImports

open BigOperators Int Real

noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat

def Target : Prop := ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ)

#check Classical.choice
#check Classical.decEq Prop
#check Classical.propComplete
#check Classical.choice (p := Target)
#check (Classical.choice : Nonempty Target → Target)
#check (Classical.decEq Target True)
#check (propext : (Target ↔ True) → Target = True)

example : Decidable Target := Classical.propDecidable Target
#print axioms Target
