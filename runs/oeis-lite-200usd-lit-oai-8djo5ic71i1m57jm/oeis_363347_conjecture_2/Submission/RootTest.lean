import FormalConjectures.Util.ProblemImports
example (p:ℕ) [NeZero p] (z:ZMod p) (hz:z^2=(5:ZMod p)) (hge:5≤z.val^2) : p ∣ z.val^2 - 5 := by
  have hzv : ((z.val^2 : ℕ) : ZMod p) = ((5 : ℕ) : ZMod p) := by
    rw [Nat.cast_pow, ZMod.natCast_zmod_val]
    simpa using hz
  rw [ZMod.natCast_eq_natCast_iff] at hzv
  exact (Nat.modEq_iff_dvd' hge).mp hzv.symm
