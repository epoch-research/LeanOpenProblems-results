import FormalConjectures.Util.ProblemImports
open Nat Finset

def A352628 (n : ℕ) : ℕ :=
  let S : Finset ℕ := range (n + 1)
  let Q := S.product (S.product (S.product S))
  Q.sum fun p =>
    let a := p.fst
    let p_bcd := p.snd
    let b := p_bcd.fst
    let p_cd := p_bcd.snd
    let c := p_cd.fst
    let d := p_cd.snd
    let E := (a^2) + (2 * b^2) + (c^4) + (2 * d^4) + (3 * c^2 * d^2)
    if E = n then 1 else 0

theorem a352628_0 : A352628 0 > 0 := by
  decide
