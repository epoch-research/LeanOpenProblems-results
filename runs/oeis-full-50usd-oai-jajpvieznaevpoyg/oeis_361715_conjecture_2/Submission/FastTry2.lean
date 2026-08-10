import FormalConjectures.Util.ProblemImports

open Nat Finset

partial def aFastAux (n todo k t acc : ℕ) : ℕ :=
  match todo with
  | 0 => acc
  | todo' + 1 =>
      let t' := t * (n - k) ^ 2 * (n + k) / (k + 1) ^ 3
      aFastAux n todo' (k+1) t' (acc + t')

def aFast (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n' + 1 => aFastAux (n'+1) n' 0 1 1

#eval (aFast (139^2) % (139^(3*2+3)))
#eval (aFast (139^(2-1)) % (139^(3*2+3)))
#eval ((aFast (139^2) + (139^(3*2+3)) - aFast (139^(2-1))) % (139^(3*2+3)))

example : ¬ ((aFast (139 ^ 2) : ℤ) ≡ aFast (139 ^ (2 - 1)) [ZMOD (139 ^ (3 * 2 + 3) : ℕ)]) := by
  native_decide
