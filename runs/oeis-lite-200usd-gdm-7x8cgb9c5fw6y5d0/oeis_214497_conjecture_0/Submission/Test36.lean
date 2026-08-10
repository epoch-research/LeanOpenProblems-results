import FormalConjectures.Util.ProblemImports

theorem test_types (P : Prop) : True := by
  let Q := PLift P → False
  let R := PLift Q → False
  let S := PLift R → False
  let T := PLift S → False
  let U := PLift T → False

  -- y2 has type: PLift Q → False, i.e., Q → False i.e., (PLift P → False) → False. Wait, y2 is in MyInhabited (PLift Q), so the Sum.inr of that has type: PLift Q → False.
  -- y3 is in MyInhabited (PLift R), so Sum.inr has type PLift R → False.
  -- PLift R → False is (PLift (PLift Q → False) → False) → False.
  -- y4 is in MyInhabited (PLift S), so Sum.inr has type PLift S → False.
  -- PLift S → False is (PLift (PLift R → False) → False) → False.
  trivial
