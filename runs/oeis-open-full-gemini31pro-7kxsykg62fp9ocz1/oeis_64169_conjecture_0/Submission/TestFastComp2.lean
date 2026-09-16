import FormalConjectures.Util.ProblemImports
open Rat

def fast_A064169_aux (n : ℕ) (acc : ℚ) : ℚ :=
  match n with
  | 0 => acc
  | n' + 1 => fast_A064169_aux n' (acc + (n' + 1 : ℚ)⁻¹)

def fast_A064169 (n : ℕ) : ℕ :=
  let hn := fast_A064169_aux n 0
  Int.natAbs (hn.num - hn.den)

lemma H_16842 : fast_A064169 50000 % 50002 = 17489 := by
  native_decide
