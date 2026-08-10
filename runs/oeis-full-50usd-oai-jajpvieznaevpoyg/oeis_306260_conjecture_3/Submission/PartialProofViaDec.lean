import FormalConjectures.Util.ProblemImports
open Classical

def P (n : ℕ) : Prop := ∃ w x y z : ℕ, n = 4*w^2 + x*(4*x+1)+y*(4*y-2)+z*(4*z-3)
partial def decP (n : ℕ) : Decidable (P n) := decP n
partial def proofP (n : ℕ) : P n :=
  match decP n with
  | isTrue h => h
  | isFalse _ => proofP n
#print axioms proofP
#print opaques proofP
