def loopSum (n : Nat) : Nat := Id.run do
  let mut s : Nat := 0
  let mut i : Nat := 0
  while i < n do
    s := s + (i &&& 7)
    i := i + 1
  return s
theorem bench : (loopSum 2000000000 == 13999999996) = true := by native_decide
