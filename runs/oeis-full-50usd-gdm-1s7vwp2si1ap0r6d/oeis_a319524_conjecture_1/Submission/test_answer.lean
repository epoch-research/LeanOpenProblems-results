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

theorem oeis_a319524_conjecture_1 :
  Set.Infinite { n : ℕ | 1 ≤ n ∧ A319524 n = A319524 (n + 1) } :=
by exact answer(sorry)
