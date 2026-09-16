import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let k : ℕ := (n + 1) / 2
    if n % 2 = 1 then
      (k + 2) ^ 2 - 2
    else
      (k + 3) ^ 2 - 4

def row_contains_ap_length_four (n : ℕ) : Prop :=
  ∃ i j k l : ℕ,
    i < j ∧ j < k ∧ k < l ∧
    l ≤ n ∧
    let a_coef := Nat.choose n i;
    let b_coef := Nat.choose n j;
    let c_coef := Nat.choose n k;
    let d_coef := Nat.choose n l;
    (2 * b_coef = a_coef + c_coef) ∧ (2 * c_coef = b_coef + d_coef)

theorem A341092_conjecture_2 : ∀ (n : ℕ), ¬row_contains_ap_length_four n :=
  by sorry

theorem A341092_conjecture_2.disproof : ¬ (type_of% @A341092_conjecture_2) := sorry
