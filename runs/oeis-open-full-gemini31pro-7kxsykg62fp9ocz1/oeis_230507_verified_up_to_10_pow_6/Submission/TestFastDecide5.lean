def checkArray (n : Nat) : Bool :=
  let arr := Array.mk (List.range n)
  arr.all (fun _ => true)

theorem check_100000 : checkArray 100000 = true := by decide
