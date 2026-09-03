import Submission.DiscreteRotationMassExplore
import Submission.ShortOrbitNaturalExplore

/-! Expected-mass-sensitive versions of the deterministic ordinary carry
bound. Both carries and their different coarse row sums are retained. -/
namespace Erdos66MassSensitivePhaseCarry
open Erdos66DiscreteRotationMass Erdos66DiscreteRotationBridge
  Erdos66ShortOrbitCarry Erdos66ShortOrbitNatural Erdos66IntegerBlock
open AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 1600000
variable (M : ℕ) [NeZero M]

/-- The same explicit phase as before, with the discrepancy logarithm
charged to the expected endpoint mass. -/
theorem mass_sensitive_natural_carry (C : ℕ → Finset (ZMod M)) (hC : Antitone C)
    (q t : ℕ) (hq : 0<q) (ht : t<M) (horizon : (q+1)^2≤M) :
    |(sumRep (blockSet M (phasedRows M C (phase M))) (q*M+t) : ℝ)-
      (((t+1 : ℕ) : ℝ)/M*phaseMass M C (phase M) q t+
        (1-((t+1 : ℕ) : ℝ)/M)*phaseMass M C (phase M) (q-1) t)| ≤
      (60+100*Real.log (((q+1 : ℕ) : ℝ)*((t+1 : ℕ) : ℝ)/M+1))*
        (halfMass M C (phase M) q t+halfMass M C (phase M) (q-1) t) := by
  have harg : 1≤((q+1 : ℕ) : ℝ)*((t+1 : ℕ) : ℝ)/M+1 := by
    have : (0 : ℝ)≤((q+1 : ℕ) : ℝ)*((t+1 : ℕ) : ℝ)/M := by positivity
    linarith
  have hE : 0≤30+50*Real.log (((q+1 : ℕ) : ℝ)*((t+1 : ℕ) : ℝ)/M+1) :=
    add_nonneg (by norm_num) (mul_nonneg (by norm_num) (Real.log_nonneg harg))
  have hh := natural_short_orbit_error M C hC (phase M) q t hq ht _ hE
    (phase_mass_intervalBound M (q+1) t horizon ht)
  convert hh using 1
  ring

/-- Complementing the endpoint window improves the bound near either end
of a low-digit block, without changing the ordinary representation mean. -/
theorem balanced_mass_natural_carry (C : ℕ → Finset (ZMod M)) (hC : Antitone C)
    (q t : ℕ) (hq : 0<q) (ht : t<M) (horizon : (q+1)^2≤M) :
    |(sumRep (blockSet M (phasedRows M C (phase M))) (q*M+t) : ℝ)-
      (((t+1 : ℕ) : ℝ)/M*phaseMass M C (phase M) q t+
        (1-((t+1 : ℕ) : ℝ)/M)*phaseMass M C (phase M) (q-1) t)| ≤
      (60+100*Real.log (((q+1 : ℕ) : ℝ)*
        min (((t+1 : ℕ) : ℝ)/M) (1-((t+1 : ℕ) : ℝ)/M)+1))*
        (halfMass M C (phase M) q t+halfMass M C (phase M) (q-1) t) := by
  have hM : (0 : ℝ)<M := by exact_mod_cast NeZero.pos M
  have hρ : ((t+1 : ℕ) : ℝ)/M≤1 :=
    (div_le_one hM).mpr (by exact_mod_cast Nat.succ_le_iff.mpr ht)
  have hm : (0 : ℝ)≤ min (((t+1 : ℕ) : ℝ)/M) (1-((t+1 : ℕ) : ℝ)/M) :=
    le_min (by positivity) (sub_nonneg.mpr hρ)
  have harg : 1≤((q+1 : ℕ) : ℝ)*
      min (((t+1 : ℕ) : ℝ)/M) (1-((t+1 : ℕ) : ℝ)/M)+1 := by
    have := mul_nonneg (Nat.cast_nonneg (q+1) : (0 : ℝ)≤((q+1 : ℕ) : ℝ)) hm
    linarith
  have hE : 0≤30+50*Real.log (((q+1 : ℕ) : ℝ)*
      min (((t+1 : ℕ) : ℝ)/M) (1-((t+1 : ℕ) : ℝ)/M)+1) :=
    add_nonneg (by norm_num) (mul_nonneg (by norm_num) (Real.log_nonneg harg))
  have hh := natural_short_orbit_error M C hC (phase M) q t hq ht _ hE
    (phase_balanced_intervalBound M (q+1) t horizon ht)
  convert hh using 1
  ring

end Erdos66MassSensitivePhaseCarry
