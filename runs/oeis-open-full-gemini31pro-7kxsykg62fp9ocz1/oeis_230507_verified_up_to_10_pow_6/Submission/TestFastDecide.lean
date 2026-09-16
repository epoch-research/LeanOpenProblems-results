def sumLoop (n i acc : Nat) : Nat :=
  if h : i > n then acc
  else sumLoop n (i + 1) (acc + i)
termination_by n + 1 - i

theorem sum_1000 : sumLoop 1000 0 0 = 500500 := by decide
