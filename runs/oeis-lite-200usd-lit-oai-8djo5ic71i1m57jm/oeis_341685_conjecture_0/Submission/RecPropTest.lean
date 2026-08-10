import FormalConjectures.Util.ProblemImports

theorem badAcc : Acc (fun _ _ : Unit => True) () := by
  let rec acc : Acc (fun _ _ : Unit => True) () := Acc.intro () (fun y hy => acc)
  exact acc

theorem bad : False := by
  have h : WellFounded (fun _ _ : Unit => True) := ⟨fun _ => badAcc⟩
  have := h.apply () () trivial
  exact False.elim (by
    -- no direct false from Acc
    sorry)
