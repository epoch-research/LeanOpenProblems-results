import Mathlib

def k := 509203
def val (m : ℕ) := k * (2 ^ m) - 1

#eval (val 1).Prime
#eval (val 2).Prime
#eval (val 3).Prime
#eval (val 4).Prime
#eval (val 5).Prime
