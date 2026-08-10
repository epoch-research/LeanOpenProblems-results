import FormalConjectures.Util.ProblemImports

-- Try to derive false from Quot.sound on a universal relation, should fail.
def Q := Quot (fun _ _ : Bool => True)
example : Quot.mk (fun _ _ : Bool => True) true = Quot.mk (fun _ _ : Bool => True) false := Quot.sound trivial

example : False := by
  have h : Quot.mk (fun _ _ : Bool => True) true = Quot.mk (fun _ _ : Bool => True) false := Quot.sound trivial
  -- no way to extract true=false from quotient equality
  fail_if_success injection h
  aesop
