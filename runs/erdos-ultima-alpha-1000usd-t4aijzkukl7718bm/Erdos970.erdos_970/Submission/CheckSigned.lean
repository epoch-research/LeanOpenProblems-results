import FormalConjecturesUtil
namespace Test
open Finset
abbrev Pattern := Finset (Fin 6)
def prime : Fin 6 → ℕ := ![2,3,5,7,11,13]
def variance (Q : Pattern) : ℚ := ∏ i ∈ Q, ((prime i - 1 : ℕ) : ℚ)
def height (Q : Pattern) : ℕ := ∏ i ∈ Q, prime i + 1
def base (Q : Pattern) : ℚ := ((24192 - height Q : ℕ) : ℚ) / variance Q
#print base
#eval base ∅
#reduce base ∅
example : 0 ≤ base ∅ := by decide +kernel
example : ∀ Q : Pattern, 0 ≤ base Q := by decide +kernel
end Test
#print Test.height
#eval Test.height {0}
#eval Test.height {0,1}
#print Test.variance
