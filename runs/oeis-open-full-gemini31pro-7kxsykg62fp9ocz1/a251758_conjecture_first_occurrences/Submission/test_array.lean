def make_sieve (n : Nat) : Array Nat :=
  let arr := mkArray n 0
  arr.set! 0 1

theorem test_arr : (make_sieve 6678671).size = 6678671 := by decide
