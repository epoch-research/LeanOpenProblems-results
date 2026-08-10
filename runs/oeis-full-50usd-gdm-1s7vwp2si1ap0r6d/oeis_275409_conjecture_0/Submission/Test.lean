import FormalConjectures.Util.ProblemImports

open Nat Finset

def a_test (n : ℕ) : ℕ :=
  let is_sq (k : ℕ) : Bool := k.sqrt * k.sqrt == k

  let M : ℕ := n.sqrt + 1
  let R : Finset ℕ := range M

  let search_space : Finset (ℕ × (ℕ × (ℕ × ℕ))) := R.product (R.product (R.product R))

  search_space.sum fun p : ℕ × (ℕ × (ℕ × ℕ)) =>
    let w := p.fst
    let x := p.snd.fst
    let y := p.snd.snd.fst
    let z := p.snd.snd.snd

    let sum_sq := 2 * w^2 + x^2 + y^2 + z^2
    let lin_comb := w + x + 2 * y + 4 * z

    if sum_sq = n ∧ is_sq lin_comb
    then 1
    else 0

#eval a_test 0
#eval a_test 1
#eval a_test 2
#eval a_test 3
#eval a_test 10
