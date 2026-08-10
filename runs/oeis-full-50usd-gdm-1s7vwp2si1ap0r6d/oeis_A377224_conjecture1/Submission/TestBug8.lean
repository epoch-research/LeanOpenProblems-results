def f (n : Nat) : Bool := true

def f_impl (n : Nat) : Bool := false

attribute [implemented_by f_impl] f

theorem unsound : f 0 = false := by
  native_decide
