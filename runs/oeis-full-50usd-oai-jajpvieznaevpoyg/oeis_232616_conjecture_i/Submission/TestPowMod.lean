import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0

def powMod (a e m : Nat) : Nat :=
  match e with
  | 0 => 1 % m
  | e+1 =>
      let r := powMod ((a*a)%m) ((e+1)/2) m
      if (e+1) % 2 = 0 then r else (r*a)%m
termination_by e
example : powMod 2 29400 137543 = 1 := by decide
example : powMod 2 29400 550172 = 524289 := by decide
