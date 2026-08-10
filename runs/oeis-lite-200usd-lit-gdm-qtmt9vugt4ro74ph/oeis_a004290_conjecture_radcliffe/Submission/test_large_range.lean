import FormalConjectures.Util.ProblemImports

def check_digits_01_fuel (fuel : Nat) (n : Nat) : Bool :=
  match fuel with
  | 0 => true
  | f + 1 =>
    if n = 0 then true
    else
      let d := n % 10
      (d == 0 || d == 1) && check_digits_01_fuel f (n / 10)

-- We use witness_fast which is already defined in Spec_orig.lean, but let's define a mock for testing speed
-- Or wait, we can just use witness_fast if we import or copy it.
-- Let's see if we can run a simple check.
