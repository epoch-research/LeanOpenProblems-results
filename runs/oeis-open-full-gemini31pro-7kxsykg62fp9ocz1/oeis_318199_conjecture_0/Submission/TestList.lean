def sumList (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h::t => h + sumList t

theorem test : sumList (List.range 5000) = 12497500 := by decide
