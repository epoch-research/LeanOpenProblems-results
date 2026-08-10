import FormalConjectures.Util.ProblemImports
open Nat

def A216265 (n : ℕ) : ℕ := Nat.primeCounting (n ^ 3) - Nat.primeCounting (n ^ 3 - n)

unsafe def unsafePr (n : ℕ) (h : n > 13) : A216265 n > 0 := unsafeCast True.intro
@[implemented_by unsafePr]
def safePr (n : ℕ) (h : n > 13) : A216265 n > 0 := by
  exact safePr n h

theorem useSafePr (n : ℕ) (h : n > 13) : A216265 n > 0 := safePr n h
#print axioms useSafePr
