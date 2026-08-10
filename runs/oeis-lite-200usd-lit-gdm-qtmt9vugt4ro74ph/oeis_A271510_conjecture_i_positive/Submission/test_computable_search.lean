import Mathlib

open Nat

def find_sol (n : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let is_square (k : ℕ) : Prop := k.sqrt * k.sqrt = k
  let bound := n.sqrt
  let R : Finset ℕ := Finset.range (bound + 1)
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) := R.product R |>.product R |>.product R
  let filtered := search_space.filter fun p =>
    let x := p.fst.fst.fst
    let y := p.fst.fst.snd
    let z := p.fst.snd
    let w := p.snd
    x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
    x ≥ y ∧
    is_square (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2)
  match filtered.toList with
  | [] => (0, 0, 0, 0)
  | p :: _ => (((p.1.1.1, p.1.1.2), p.1.2), p.2)

#eval find_sol 10

lemma test_sol_10 : (find_sol 10).1^2 + (find_sol 10).2.1^2 + (find_sol 10).2.2.1^2 + (find_sol 10).2.2.2^2 = 10 := by
  decide
