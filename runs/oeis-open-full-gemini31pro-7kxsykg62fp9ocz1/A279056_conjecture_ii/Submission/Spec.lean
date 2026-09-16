import FormalConjectures.Util.ProblemImports

open Nat Int Finset

def A279056 (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  let B : ℕ := n.sqrt + 1
  let R : Finset ℕ := range B
  let S := ((R.product R).product R).product R
  Finset.card $ S.filter fun p =>
    let w := p.fst.fst.fst
    let x := p.fst.fst.snd
    let y := p.fst.snd
    let z := p.snd
    let square_cond : Prop :=
      let val : ℤ := (x : ℤ)^3 + 4 * (y : ℤ) * (z : ℤ) * ((y : ℤ) - (z : ℤ))
      IsSquare val
    w > 0 ∧ w^2 + x^2 + y^2 + z^2 = n ∧ square_cond

def B_A279056 (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  let B : ℕ := n.sqrt + 1
  let R : Finset ℕ := range B
  let S := ((R.product R).product R).product R
  Finset.card $ S.filter fun p =>
    let w := p.fst.fst.fst
    let x := p.fst.fst.snd
    let y := p.fst.snd
    let z := p.snd
    let square_cond : Prop :=
      let val : ℤ := (x : ℤ)^3 + 8 * (y : ℤ) * (z : ℤ) * (2 * (y : ℤ) - (z : ℤ))
      IsSquare val
    w > 0 ∧ w^2 + x^2 + y^2 + z^2 = n ∧ square_cond

theorem A279056_conjecture_ii (n : ℕ) (hn : n > 0) : 0 < B_A279056 n := sorry

theorem A279056_conjecture_ii.disproof : ¬ (type_of% @A279056_conjecture_ii) := sorry
