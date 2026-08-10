import FormalConjectures.Util.ProblemImports

open Nat

noncomputable def A319524 (n : ℕ) : ℕ :=
  let p (k : ℕ) : ℕ := Nat.nth Nat.Prime k
  let Pn    := p (n - 1)
  let Pnp1  := p n
  let Pnp2  := p (n + 1)

  sInf { x : ℕ |
    ∃ (m m' : ℕ),
      1 ≤ m ∧ 1 ≤ m' ∧
      x = Pn + m * Pnp1 ∧
      x = Pnp1 + m' * Pnp2
  }

#eval A319524 1
#eval A319524 2
#eval A319524 3
#eval A319524 4
#eval A319524 5
#eval A319524 6
#eval A319524 7
#eval A319524 8
#eval A319524 9
#eval A319524 10
