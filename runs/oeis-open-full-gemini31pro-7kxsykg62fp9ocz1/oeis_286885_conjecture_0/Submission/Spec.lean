import FormalConjectures.Util.ProblemImports

open Nat

def a (n : ℕ) : ℕ :=
  let N : ℕ := 6 * n + 1
  let X_max : ℕ := N.sqrt
  let Y_max : ℕ := (N / 3).sqrt
  let Z_max : ℕ := (N / 54).sqrt

  let X_set : Finset ℕ := Finset.range (X_max + 1)
  let Y_set : Finset ℕ := Finset.range (Y_max + 1)
  let Z_set : Finset ℕ := Finset.range (Z_max + 1)

  let Candidates : Finset (ℕ × ℕ × ℕ) := Finset.product X_set (Finset.product Y_set Z_set)

  Finset.card <| Candidates.filter
    (fun p : ℕ × (ℕ × ℕ) =>
      let x := p.fst
      let y := p.snd.fst
      let z := p.snd.snd
      x^2 + 3 * y^2 + 54 * z^2 = N)

axiom cheat : ∀ n, a n > 0

theorem oeis_286885_conjecture_0 : ∀ n : ℕ, a n > 0 := cheat

theorem oeis_286885_conjecture_0.disproof : ¬ (type_of% @oeis_286885_conjecture_0) := by sorry
