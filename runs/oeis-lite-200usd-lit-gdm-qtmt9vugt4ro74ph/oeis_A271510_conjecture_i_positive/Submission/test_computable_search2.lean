import Mathlib

open Nat

def search_y (n w z y : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  match y with
  | 0 => none
  | y' + 1 =>
    let y := y'
    if n ≥ w^2 + z^2 + y^2 then
      let rem := n - w^2 - z^2 - y^2
      let x := rem.sqrt
      if x^2 = rem ∧ x ≥ y ∧ (x^2 + 8*y^2 + 16*z^2).sqrt * (x^2 + 8*y^2 + 16*z^2).sqrt = x^2 + 8*y^2 + 16*z^2 then
        some (x, y, z, w)
      else
        search_y n w z y'
    else
      search_y n w z y'

def search_z (n w z : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  match z with
  | 0 => none
  | z' + 1 =>
    let z := z'
    match search_y n w z (n.sqrt + 1) with
    | some sol => some sol
    | none => search_z n w z'

def search_w (n w : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  match w with
  | 0 => none
  | w' + 1 =>
    let w := w'
    match search_z n w (n.sqrt + 1) with
    | some sol => some sol
    | none => search_w n w'

def find_sol (n : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  match search_w n (n.sqrt + 1) with
  | some sol => sol
  | none => (0, 0, 0, 0)

#eval find_sol 10

lemma test_sol_10 : let s := find_sol 10; s.1^2 + s.2.1^2 + s.2.2.1^2 + s.2.2.2^2 = 10 ∧ s.1 ≥ s.2.1 := by
  decide
