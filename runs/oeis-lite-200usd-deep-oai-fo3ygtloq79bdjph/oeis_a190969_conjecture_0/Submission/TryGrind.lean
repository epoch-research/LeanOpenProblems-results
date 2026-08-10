import FormalConjectures.Util.ProblemImports

def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => 5 * a (n + 1) - 8 * a n
open Finset Nat
open scoped BigOperators

theorem test (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) :
    let K (n : ℕ) := ZMod (p ^ n)
    let S (n : ℕ) : K n :=
        (range p).sum fun k =>
            let num : K n := (a (4 * k) : K n) * ((choose (2 * k) k : ℕ) : K n) ^ 3
            let den : K n := ((-4096 : ℤ) : K n) ^ k
            num * den⁻¹
    S 2 = 0 ∧ (p % 7 ∈ ({1, 2, 4} : Set ℕ) → S 3 = 0) := by
  have hp23 : p ^ 2 ≠ p ^ 3 := by
    have hp1 : (1 : ℕ) < p := hp.one_lt
    nlinarith [hp1]
  grind [Nat.Prime.ne_zero, Nat.Prime.ne_one]
