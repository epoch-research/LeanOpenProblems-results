import FormalConjectures.Util.ProblemImports
abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

example : Target := by
  classical
  let e := Classical.propComplete Target
  rcases e with h | h
  · exact h
  · have ht : Target = False := h
    have htf : Target ↔ False := by simpa [ht]
    -- cannot prove Target, but try by contradiction
    exfalso
    exact? 
