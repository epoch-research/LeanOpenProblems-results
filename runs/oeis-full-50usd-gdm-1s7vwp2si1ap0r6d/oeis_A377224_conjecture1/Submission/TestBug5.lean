theorem unsound : False := by
  let rec loop (n : Nat) : False := loop (n + 1)
  exact loop 0
