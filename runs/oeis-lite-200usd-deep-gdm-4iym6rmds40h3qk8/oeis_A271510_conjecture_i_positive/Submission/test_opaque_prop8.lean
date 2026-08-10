import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ := 1

structure MyType (P : Prop) where
  is_true : Bool
  proof : is_true = true → P
  loop : is_true = false → MyType P

partial def get_default (P : Prop) : MyType P :=
  ⟨false, fun h => by contradiction, fun _ => get_default P⟩

instance (P : Prop) : Inhabited (MyType P) :=
  ⟨get_default P⟩
