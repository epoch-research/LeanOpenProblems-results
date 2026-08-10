import FormalConjectures.Util.ProblemImports
open Cardinal

#synth Algebra.Transcendental ℚ (Padic 3)
#check Algebra.Transcendental.transcendental
#check Algebra.transcendental_iff_not_isAlgebraic
#check Algebra.IsAlgebraic.cardinalMk_le_max
#check Padic.denseRange_ratCast
#check Cardinal.mk_real
#check Padic.cardinalMk_eq_continuum
#check cardinalMk_padic
#check Padic.instNontrivial

example [Algebra.Transcendental ℚ (Padic 3)] : ∃ x : Padic 3, ¬ IsAlgebraic ℚ x :=
  Algebra.Transcendental.transcendental (R := ℚ) (A := Padic 3)

example [Algebra.Transcendental ℚ (Padic 3)] : ¬ IsAlgebraic ℚ (Classical.choose (Algebra.Transcendental.transcendental (R := ℚ) (A := Padic 3))) := by
  exact (Classical.choose_spec (Algebra.Transcendental.transcendental (R := ℚ) (A := Padic 3)))
