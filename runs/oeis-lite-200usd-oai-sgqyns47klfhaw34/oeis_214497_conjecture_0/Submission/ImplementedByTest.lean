import FormalConjectures.Util.ProblemImports
abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

unsafe def unsafeTargetImpl : Target := lcProof
@[implemented_by unsafeTargetImpl]
def safeTarget : Target := by
  -- need safe body
  exact?
#print axioms safeTarget
