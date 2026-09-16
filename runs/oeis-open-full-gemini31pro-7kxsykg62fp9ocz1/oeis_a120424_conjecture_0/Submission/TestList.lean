def lst : List Nat := [1, 2, 3, 4, 5] -- just a test
def check : Bool :=
  lst.all (fun x => x > 0)
theorem ok : check = true := by decide
