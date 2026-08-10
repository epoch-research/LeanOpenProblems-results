import FormalConjectures.Util.ProblemImports

lemma test_nlinarith (i s : Nat) : 4^i * (10 * 16^s + 16 * 4^s + 10) ≥ 10 * 16^s := by
  have hA : 4^i ≥ 1 := by
    have : 4^i > 0 := by positivity
    omega
  have hB : 10 * 16^s + 16 * 4^s + 10 ≥ 10 * 16^s := by omega
  have hC : 10 * 16^s ≥ 0 := by omega
  nlinarith
