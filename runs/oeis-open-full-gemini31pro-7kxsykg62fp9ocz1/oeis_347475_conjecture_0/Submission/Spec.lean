import FormalConjectures.Util.ProblemImports

open Nat Filter Finset

def only_odd_digits (n : ℕ) : Prop :=
  (Nat.digits 10 n).all (fun d => d % 2 = 1)

noncomputable instance only_odd_digits_decidable (n : ℕ) : Decidable (only_odd_digits n) := Classical.propDecidable _

def is_A347475_term (k : ℕ) : Prop :=
  k > 0 ∧ only_odd_digits k ∧ only_odd_digits (k * (k + 1) / 2)

noncomputable instance is_A347475_term_decidable (k : ℕ) : Decidable (is_A347475_term k) := Classical.propDecidable _

noncomputable def A355276 (L : ℕ) : ℕ :=
  if L = 0 then 0 else
  (Finset.filter is_A347475_term (Ico (10^(L - 1)) (10^L))).card

theorem oeis_347475_conjecture_0 :
  Tendsto A355276 atTop atTop :=
by sorry

theorem oeis_347475_conjecture_0.disproof : ¬ (type_of% @oeis_347475_conjecture_0) :=
by sorry
