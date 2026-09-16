def big_mul : Nat := Id.run do
  let mut a : Nat := 3
  for i in [0:25] do
    a := a * a
  return a

#eval (big_mul % 10)
