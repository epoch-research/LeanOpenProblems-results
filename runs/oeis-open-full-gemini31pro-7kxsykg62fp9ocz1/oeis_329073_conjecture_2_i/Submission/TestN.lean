def f (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | N@(_ + 1) => N

#eval f 5
