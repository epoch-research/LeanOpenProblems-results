import FormalConjectures.Util.ProblemImports

inductive BadEq : Prop where
| intro : (BadEq = False) → BadEq

example : False := by
  let hbeq : BadEq = False := propext ⟨fun b => by cases b with | intro h => exact False.elim (by exact Eq.mp h b), fun f => False.elim f⟩
  have b : BadEq := BadEq.intro hbeq
  exact Eq.mp hbeq b

#print axioms _example
