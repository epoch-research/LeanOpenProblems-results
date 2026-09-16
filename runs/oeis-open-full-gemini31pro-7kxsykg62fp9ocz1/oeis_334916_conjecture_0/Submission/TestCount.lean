partial def countBillion (n : Nat) : Nat :=
  let rec loop (i : Nat) (acc : Nat) : Nat :=
    if i == 0 then acc else loop (i - 1) (acc + 1)
  loop n 0

#eval! countBillion 1000000000
