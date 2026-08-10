import FormalConjectures.Util.ProblemImports

def a (n : Nat) : Nat := n

theorem a_745_pos : a 745 > 0 := by dsimp [a]; omega

class MyNonempty (B : Type) where
  val : B

partial def safe_cast {A B : Type} [inst : MyNonempty B] (x : A) : B :=
  safe_cast x

#print axioms safe_cast
