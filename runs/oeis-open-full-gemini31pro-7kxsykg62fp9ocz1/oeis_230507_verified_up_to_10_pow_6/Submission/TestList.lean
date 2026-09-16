def checkList (n : Nat) : Bool :=
  let l := List.range n
  l.all (fun _ => true)

theorem t1 : checkList 100000 = true := by decide
