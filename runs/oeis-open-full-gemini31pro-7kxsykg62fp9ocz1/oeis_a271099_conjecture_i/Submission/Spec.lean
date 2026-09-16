import FormalConjectures.Util.ProblemImports

open Nat Finset

def A271099 (n : ℕ) : ℕ :=
  let R := range (n + 1)
  Finset.sum R fun u =>
  Finset.sum R fun v =>
  Finset.sum R fun x =>
  Finset.sum R fun y =>
  Finset.sum R fun z =>
    if u ≤ v ∧ x ≤ y ∧ u ^ 3 + v ^ 3 + 2 * x ^ 3 + 2 * y ^ 3 + 3 * z ^ 3 = n then
      1
    else
      0

def A271099_lone_count_set : Finset ℕ :=
  {0, 1, 10, 14, 15, 17, 22, 38, 39, 45, 47, 50, 52, 76, 102, 103, 188, 295, 366, 534}

theorem oeis_a271099_conjecture_i :
  (∀ n : ℕ, A271099 n > 0) ∧
  (∀ n : ℕ, A271099 n = 1 ↔ n ∈ A271099_lone_count_set) :=
by sorry

theorem oeis_a271099_conjecture_i.disproof : ¬ (type_of% @oeis_a271099_conjecture_i) := answer(sorry)
