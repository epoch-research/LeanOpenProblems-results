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

def zero_set : List ℕ := [3, 10]
def one_set : List ℕ := [0, 2, 7, 8, 9, 12, 14, 15, 22, 23, 24, 25, 36, 39, 44, 45, 60, 87, 98, 106, 110, 111, 183]

def run_test : List ℕ :=
  (List.range 200).filter fun n =>
    let val := a_test n
    let cond_zero := (val > 0) == (!zero_set.contains n)
    let cond_one := (val == 1) == (one_set.contains n)
    !(cond_zero && cond_one)

#eval run_test
