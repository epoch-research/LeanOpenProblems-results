import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic

def check_prop (b : Fin 100000) : Bool :=
  (b.val + 1) > 0

theorem all_check : ∀ b : Fin 100000, check_prop b = true := by
  decide
