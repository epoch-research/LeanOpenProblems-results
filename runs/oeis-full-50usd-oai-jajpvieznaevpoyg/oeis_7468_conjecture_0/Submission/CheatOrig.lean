import FormalConjectures.Util.ProblemImports
noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

unsafe def decOrigUnsafe : Decidable (∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38) :=
  isTrue (unsafeCast ())
@[implemented_by decOrigUnsafe]
noncomputable def decOrig : Decidable (∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38) :=
  Classical.propDecidable _

local instance : Decidable (∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38) := decOrig

theorem oeis_7468_conjecture_0 : ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := by
  native_decide
#print axioms oeis_7468_conjecture_0
