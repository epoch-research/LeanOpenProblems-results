import Mathlib

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem test_padic_le_one (x : Padic 5) (h : x = 0) : x ∈ PadicInt.subring 5 := by
  rw [h]
  exact Subring.zero_mem (PadicInt.subring 5)
