import FormalConjectures.Util.ProblemImports

def A271510 (n : ℕ) : ℕ := 1

theorem proof_tautology (P : Prop) : (((((False → P) → P) → P) → P) → P) → P :=
  fun H => H (fun G => G (fun (f : False) => False.elim f))

#print axioms proof_tautology
