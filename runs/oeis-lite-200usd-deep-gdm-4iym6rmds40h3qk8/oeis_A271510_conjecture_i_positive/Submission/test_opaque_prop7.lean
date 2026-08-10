import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ := 1

structure MyType (P : Prop) where
  is_true : Bool
  proof : is_true = true → P
  loop : is_true = false → MyType P

instance (P : Prop) : Inhabited (MyType P) :=
  let rec default_val : MyType P :=
    ⟨false, fun h => by contradiction, fun _ => default_val⟩
  ⟨default_val⟩
