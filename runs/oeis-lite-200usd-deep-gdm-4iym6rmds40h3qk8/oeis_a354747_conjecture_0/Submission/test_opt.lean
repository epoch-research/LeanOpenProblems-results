import Mathlib.Data.Nat.Basic

def N : ℕ := 2 * 100943 * 3 ^ 39101 - 1

instance : NeZero N := ⟨by
  unfold N
  have h_pow : 3 ^ 39101 > 0 := Nat.pow_pos (by decide)
  omega⟩

attribute [irreducible] N

-- Let's see if we can still use N in types without unfolding it
def test_val : ZMod N := 1
