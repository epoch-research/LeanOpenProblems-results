import FormalConjectures.Util.ProblemImports

open Nat
open scoped Nat.Prime

def A262781 (n : ℕ) : ℕ :=
  let R_x := Finset.range (Nat.sqrt n + 1)
  let R_y_z := (Finset.range (n + 1)).product (Finset.range (n + 1))

  Finset.card $
  (R_x.product R_y_z)
  |>.filter (fun p =>
    let x := p.fst
    let y := p.snd.fst
    let z := p.snd.snd

    0 < y ∧ y ≤ z ∧
    (y.Prime ∨ z.Prime) ∧
    x^2 + totient (y ^ 2) + totient (z ^ 2) = n
  )

def A262781_unit_set : Finset ℕ :=
  {3, 5, 9, 10, 17, 20, 24, 25, 31, 36, 45, 73, 80, 101, 136, 145, 388, 649}

def oeis_A262781_conjecture_statement : Prop :=
  (∀ n : ℕ, 6 < n → 0 < A262781 n) ∧
  (∀ n : ℕ, A262781 n = 1 ↔ n ∈ A262781_unit_set) ∧
  (∀ n : ℕ, 4 < n →
    ∃ (p x y : ℕ),
      p.Prime ∧ 0 < x ∧ 0 < y ∧
      p ≤ x ∧ x ≤ y ∧
      totient (p ^ 2) + totient (x ^ 2) + totient (y ^ 2) = 2 * n)

theorem oeis_A262781_conjecture : oeis_A262781_conjecture_statement := by sorry

theorem oeis_A262781_conjecture.disproof : ¬ (type_of% @oeis_A262781_conjecture) := by sorry
#eval A262781 36
