import FormalConjectures.Util.ProblemImports

open Nat Filter Finset

/-- Predicate for a natural number having only odd digits in base 10. -/
def only_odd_digits (n : ℕ) : Prop :=
  (Nat.digits 10 n).all (fun d => d % 2 = 1)

-- This predicate is computationally decidable. We use a noncomputable instance via Classical.
noncomputable instance only_odd_digits_decidable (n : ℕ) : Decidable (only_odd_digits n) := Classical.propDecidable _

/-- The property defining terms of A347475: $k$ and $T(k) = k(k+1)/2$ have only odd digits. -/
def is_A347475_term (k : ℕ) : Prop :=
  k > 0 ∧ only_odd_digits k ∧ only_odd_digits (k * (k + 1) / 2)

-- This predicate is also decidable.
noncomputable instance is_A347475_term_decidable (k : ℕ) : Decidable (is_A347475_term k) := Classical.propDecidable _

/-- A355276: The number of $L$-digit terms in A347475. -/
noncomputable def A355276 (L : ℕ) : ℕ :=
  if L = 0 then 0 else
  (Finset.filter is_A347475_term (Ico (10^(L - 1)) (10^L))).card

def oeis_347475_conjecture_0_prop : Prop :=
  answer(Tendsto A355276 atTop atTop ↔ True)

theorem test1 : Tendsto A355276 atTop atTop := by
  have h_eq : (Tendsto A355276 atTop atTop ↔ True) := oeis_347475_conjecture_0_prop
  sorry
