import FormalConjectures.Util.ProblemImports
open Rat

def fast_A064169_aux (n : ℕ) (acc : ℚ) : ℚ :=
  match n with
  | 0 => acc
  | n' + 1 => fast_A064169_aux n' (acc + (n' + 1 : ℚ)⁻¹)

def fast_A064169 (n : ℕ) : ℕ :=
  let hn := fast_A064169_aux n 0
  Int.natAbs (hn.num - hn.den)

lemma test_500k : fast_A064169 500000 % 500002 > 0 := by
  native_decide
