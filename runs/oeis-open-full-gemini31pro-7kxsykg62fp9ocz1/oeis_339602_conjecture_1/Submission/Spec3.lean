import FormalConjectures.Util.ProblemImports

def A030101 (n : Nat) : Nat :=
  Nat.ofDigits 2 (List.reverse (Nat.digits 2 n))

def a : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => (a n).xor (A030101 (a (n + 1))) + 1

#eval a 2
#eval a 3
#eval a 4
