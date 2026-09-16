import Mathlib

def check (m : ℕ) : Bool :=
  (509203 * (2 ^ m) - 1).Prime

#eval (List.range 24).map (fun i => check (i + 1))
