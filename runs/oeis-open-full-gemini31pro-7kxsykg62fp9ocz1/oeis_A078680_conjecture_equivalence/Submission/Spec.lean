import FormalConjectures.Util.ProblemImports
open PNat

noncomputable def A078680 (n : ℕ) : ℕ :=
  let P (m : PNat) : Prop := Nat.Prime (n * 2 ^ (m : ℕ) + 1)
  match Classical.dec (∃ m : PNat, P m) with
  | isTrue h_exist => (PNat.find h_exist).val
  | isFalse _      => 0

open Nat

theorem oeis_A078680_conjecture_equivalence :
  (A078680 (2^16) = 0 ∧ (∀ n : ℕ, 1 ≤ n ∧ n < 2^16 → A078680 n ≠ 0))
  ↔
  (∀ k : ℕ, 4 < k → ¬ Nat.Prime (fermatNumber k)) := by
  sorry

theorem oeis_A078680_conjecture_equivalence.disproof : ¬ (type_of% @oeis_A078680_conjecture_equivalence) := by
  sorry
