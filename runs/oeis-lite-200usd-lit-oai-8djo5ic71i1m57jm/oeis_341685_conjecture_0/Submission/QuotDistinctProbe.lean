import FormalConjectures.Util.ProblemImports

def QB := Quot (fun _ _ : Bool => True)

theorem qeq : Quot.mk (fun _ _ : Bool => True) true = Quot.mk (fun _ _ : Bool => True) false := Quot.sound trivial

example : Quot.mk (fun _ _ : Bool => True) true ≠ Quot.mk (fun _ _ : Bool => True) false := by
  intro h
  cases h

example : False := by
  have hne : Quot.mk (fun _ _ : Bool => True) true ≠ Quot.mk (fun _ _ : Bool => True) false := by
    intro h; cases h
  exact hne qeq
