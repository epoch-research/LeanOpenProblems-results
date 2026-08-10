import FormalConjectures.Util.ProblemImports
open Nat
abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

structure Box where
  proof : Target
-- deriving Inhabited

-- Try command deriving
-- deriving instance Inhabited for Box
-- deriving instance Nonempty for Box

structure Box2 where
  proof : Target := by
    -- no
    sorry

#check Box.mk
