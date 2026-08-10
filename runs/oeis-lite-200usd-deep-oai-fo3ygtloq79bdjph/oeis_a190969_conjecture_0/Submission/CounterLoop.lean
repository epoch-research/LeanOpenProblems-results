import FormalConjectures.Util.ProblemImports
open Finset Nat
open scoped BigOperators

def loopZ (m : ℕ) : ℕ → ℕ → ZMod m → ZMod m → ZMod m → ZMod m → ZMod m → ZMod m
| 0, _k, _b0, _b1, _c, _invden, acc => acc
| 1, _k, b0, _b1, c, invden, acc => acc + b0 * c^3 * invden
| r+2, k, b0, b1, c, invden, acc =>
    let term := b0 * c^3 * invden
    let b2 : ZMod m := (-47 : ℤ) * b1 - (4096 : ℤ) * b0
    let c2 : ZMod m := c * ((4*k+2 : ℕ) : ZMod m) * (((k+1 : ℕ) : ZMod m)⁻¹)
    let inv2 : ZMod m := invden * (((-4096 : ℤ) : ZMod m)⁻¹)
    loopZ m (r+1) (k+1) b1 b2 c2 inv2 (acc + term)

def counterVal : ZMod (130579^3) := loopZ (130579^3) 130579 0 0 45 1 1 0
#eval counterVal
#eval (counterVal = (2225898497228688 : ZMod (130579^3)))
#eval (counterVal = (0 : ZMod (130579^3)))

theorem counterVal_eq : counterVal = (2225898497228688 : ZMod (130579^3)) := by
  native_decide
