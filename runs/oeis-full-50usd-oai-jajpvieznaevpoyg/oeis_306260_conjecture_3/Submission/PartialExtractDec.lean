import FormalConjectures.Util.ProblemImports

def P (n : ℕ) : Prop := ∃ w x y z : ℕ, n = 4*w^2 + x*(4*x+1)+y*(4*y-2)+z*(4*z-3)
partial def decP (n : ℕ) : Decidable (P n) := decP n
partial def extractP (n : ℕ) (d : Decidable (P n)) : P n :=
  match d with
  | isTrue h => h
  | isFalse _ => extractP n d

theorem t (n : ℕ) : P n := extractP n (decP n)
#print axioms t
#print opaques t
