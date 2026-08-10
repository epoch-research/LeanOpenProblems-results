import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
noncomputable def xi_3_local : Padic 3 := tsum (fun k : ℕ => (Nat.factorial k : Padic 3))
#check PadicInt.exists_eq
#check PadicInt.mk
#check PadicInt.norm_le_one
#check PadicInt.mem_range_iff_norm_le_one
#check PadicInt.coe_injective
#check PadicInt.isFractionRing
#check IsIntegralClosure
#synth CompactSpace (PadicInt 3)
#synth Algebra.IsIntegral ℤ (PadicInt 3)
#synth Algebra.IsAlgebraic ℤ (PadicInt 3)
#synth IsIntegralClosure (PadicInt 3) ℤ (Padic 3)
