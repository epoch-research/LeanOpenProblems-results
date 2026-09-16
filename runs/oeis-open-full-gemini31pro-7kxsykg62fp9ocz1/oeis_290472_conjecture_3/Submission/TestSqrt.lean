def my_sqrt (n : Nat) : Nat :=
  let rec loop (x : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => x
    | f + 1 =>
      let nx := (x + n / x) / 2
      if nx < x then loop nx f else x
  if n <= 1 then n else loop n n

theorem test : my_sqrt 25 = 5 := by decide
