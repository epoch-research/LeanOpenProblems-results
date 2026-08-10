import FormalConjectures.Util.ProblemImports

example : Int.toNat (2:ℤ) = 2 := by rfl
example : (⌊(2:ℚ)⌋ : ℤ).toNat = 2 := by rw [Int.floor_intCast]; rfl
example : (⌊(181:ℚ)⌋ : ℤ).toNat = 181 := by rw [Int.floor_intCast]; rfl
example : Odd ((⌊(181:ℚ)⌋ : ℤ).toNat) := by rw [Int.floor_intCast]; norm_num
