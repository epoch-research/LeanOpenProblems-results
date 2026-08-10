import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#check FaithfulSMul.algebraMap_injective ℚ (Padic 3)
#check algebraMap ℚ (Padic 3)
#check RingHom.injective_int
#check CharZero.cast_injective
#synth FaithfulSMul ℚ (Padic 3)
example : Function.Injective (algebraMap ℚ (Padic 3)) := by exact FaithfulSMul.algebraMap_injective ℚ (Padic 3)
example : ¬ Function.Injective (algebraMap ℚ (Padic 3)) := by
  intro h
  have hz := h (show algebraMap ℚ (Padic 3) 0 = algebraMap ℚ (Padic 3) 1 by norm_num)
  norm_num at hz
