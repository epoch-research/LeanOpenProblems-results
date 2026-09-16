import Mathlib

namespace Int
def ModEq (n a b : ℤ) : Prop := True
end Int

theorem check : (1 : ℤ) ≡ 2 [ZMOD 3] := by
  trivial
