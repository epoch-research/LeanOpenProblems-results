import FormalConjectures.Util.ProblemImports

open Nat

set_option maxRecDepth 200000

def A271510 (n : ℕ) : ℕ :=
  let is_square (k : ℕ) : Prop := k.sqrt * k.sqrt = k
  let bound := n.sqrt
  let R : Finset ℕ := Finset.range (bound + 1)
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) := R.product R |>.product R |>.product R
  Finset.card $ search_space.filter fun p =>
    let x := p.fst.fst.fst
    let y := p.fst.fst.snd
    let z := p.fst.snd
    let w := p.snd
    x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
    x ≥ y ∧
    is_square (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2)

lemma sol_exists_150 : ∀ n ≤ 150, 0 < A271510 n := by
  decide





