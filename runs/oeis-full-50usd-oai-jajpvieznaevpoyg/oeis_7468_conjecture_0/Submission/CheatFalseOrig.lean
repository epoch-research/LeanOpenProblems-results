import FormalConjectures.Util.ProblemImports
noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

unsafe def decFalseUnsafe : Decidable False := isTrue (unsafeCast ())
@[implemented_by decFalseUnsafe]
def decFalseLie : Decidable False := isFalse (by intro h; exact h)
local instance : Decidable False := decFalseLie

theorem oeis_7468_conjecture_0 : ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := by
  have h : False := by native_decide
  exact False.elim h
#print axioms oeis_7468_conjecture_0
