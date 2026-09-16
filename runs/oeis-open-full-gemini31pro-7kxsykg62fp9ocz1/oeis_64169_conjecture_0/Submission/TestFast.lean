import FormalConjectures.Util.ProblemImports
open Rat
set_option maxRecDepth 1000000

def fast_harmonic_aux (n : ℕ) (acc : ℚ) : ℚ :=
  match n with
  | 0 => acc
  | n' + 1 => fast_harmonic_aux n' (acc + (n' + 1 : ℚ)⁻¹)

def fast_harmonic (n : ℕ) : ℚ := fast_harmonic_aux n 0

lemma H_16842 : (fast_harmonic 2000).num > 0 := by
  decide
