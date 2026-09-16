import FormalConjectures.Util.ProblemImports

open Nat Classical

def reverse_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let P (k : ℕ) : Prop := k > 0 ∧ n ∣ reverse_nat (k * n)
    if h_ex : ∃ k, P k then
      have HP : DecidablePred P := by infer_instance
      let k_min : ℕ := Nat.find h_ex
      k_min * n
    else
      0

theorem oeis_62567_conjecture_0 (n : ℕ) :
  2 ≤ n → (a (3^n) = 10 ^ (3 ^ (n - 2)) - 1 ↔ n = 2 ∨ n = 3 ∨ n = 4) :=
by sorry

theorem oeis_62567_conjecture_0.disproof : ¬ (type_of% @oeis_62567_conjecture_0) := by sorry
