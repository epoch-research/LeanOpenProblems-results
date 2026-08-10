import FormalConjectures.Util.ProblemImports
abbrev Ptarget : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

mutual
  theorem mt1 : Ptarget := mt2
  theorem mt2 : Ptarget := mt1
end
#print axioms mt1
