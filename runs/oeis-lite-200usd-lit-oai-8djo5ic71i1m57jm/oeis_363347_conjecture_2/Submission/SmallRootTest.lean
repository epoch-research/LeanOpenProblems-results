import FormalConjectures.Util.ProblemImports
example (p:ℕ) [NeZero p] (hroot: ((1:ℕ):ZMod p) = (5:ZMod p)) : p ∣ 4 := by
  have hzero : ((4:ℕ):ZMod p)=0 := by
    calc ((4:ℕ):ZMod p) = (5:ZMod p) - (1:ZMod p) := by norm_num
      _ = 0 := by rw [← hroot]; ring
  rwa [ZMod.natCast_eq_zero_iff] at hzero
example (p:ℕ) [NeZero p] (hroot: ((4:ℕ):ZMod p) = (5:ZMod p)) : p ∣ 1 := by
  have hzero : ((1:ℕ):ZMod p)=0 := by
    calc ((1:ℕ):ZMod p) = (5:ZMod p) - (4:ZMod p) := by norm_num
      _ = 0 := by rw [← hroot]; ring
  rwa [ZMod.natCast_eq_zero_iff] at hzero
example (p:ℕ) [NeZero p] (hroot: ((9:ℕ):ZMod p) = (5:ZMod p)) : p ∣ 4 := by
  have hzero : ((4:ℕ):ZMod p)=0 := by
    calc ((4:ℕ):ZMod p) = (9:ZMod p) - (5:ZMod p) := by norm_num
      _ = 0 := by rw [hroot]; ring
  rwa [ZMod.natCast_eq_zero_iff] at hzero
