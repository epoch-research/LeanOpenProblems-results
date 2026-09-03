import Submission.KloostermanIntervals
/-! Independent checks of incomplete Kloosterman estimates. -/
open scoped BigOperators
open Erdos821.Kloosterman
#print axioms intervalResidueWeight_pairing
#print axioms fieldFourier_intervalResidueWeight
#print axioms fourierMass_intervalResidueWeight_le
#print axioms intervalKloosterman_eq_weighted
#print axioms intervalKloosterman_norm_le_harmonic
#print axioms intervalKloosterman_norm_le_log
example {q : ℕ} [Fact q.Prime] (M : ℤ) (L : ℕ) (hL : L ≤ q)
    (a b : ZMod q) (hb : b ≠ 0) :
    ‖∑ n ∈ Finset.range L,
      if ((M+n : ℤ) : ZMod q)=0 then (0 : ℂ)
      else ZMod.stdAddChar (a*((M+n : ℤ) : ZMod q)+b*((M+n : ℤ) : ZMod q)⁻¹)‖ ≤
        Real.sqrt (Real.sqrt (3*(q : ℝ)^3)) * (2+Real.log q) :=
  intervalKloosterman_norm_le_log M L hL a b hb
