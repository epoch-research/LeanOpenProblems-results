import Submission.DiscreteRotationBridgeExplore
import Submission.ShortOrbitNaturalExplore

/-! A simultaneous explicit phase for the ordinary carry estimates of
antitone finite row palettes. This is a finite construction, not an
infinite compatibility theorem. -/
namespace Erdos66ExplicitPhaseCarry
open Erdos66ShortOrbitCarry Erdos66ShortOrbitNatural
  Erdos66DiscreteRotationBridge Erdos66IntegerBlock
open AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 1600000

variable (M : ℕ) [NeZero M]

/-- The phase depends only on the modulus, and preserves row zero exactly. -/
theorem explicit_natural_carry (C : ℕ → Finset (ZMod M)) (hC : Antitone C)
    (q t : ℕ) (hq : 0 < q) (ht : t < M) (horizon : (q+1)^2 ≤ M) :
    |(sumRep (blockSet M (phasedRows M C (phase M))) (q*M+t) : ℝ) -
      (((t+1 : ℕ) : ℝ)/M * phaseMass M C (phase M) q t +
        (1-((t+1 : ℕ) : ℝ)/M) * phaseMass M C (phase M) (q-1) t)| ≤
      50*Real.log ((q : ℝ)+2)*
        (halfMass M C (phase M) q t + halfMass M C (phase M) (q-1) t) := by
  have hE : 0 ≤ 25*Real.log (((q+1 : ℕ) : ℝ)+1) :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by have h := Nat.cast_nonneg (q+1) (α := ℝ); linarith))
  have hh := natural_short_orbit_error M C hC (phase M) q t hq ht
    (25*Real.log (((q+1 : ℕ) : ℝ)+1)) hE (phase_intervalBound M (q+1) t horizon ht)
  simp only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] at hh ⊢
  convert hh using 1
  ring

end Erdos66ExplicitPhaseCarry
