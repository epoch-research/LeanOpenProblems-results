import Submission.EveryPrimeFlatFamilyExplore

/-! Relative-error form of the every-prime finite template theorem. This
provides explicit choices of the spacing, mean, and prime threshold, but no
assertion about compatible infinite integer prefixes. -/
namespace Erdos66EveryPrimeRelativeFamily
open Erdos66EveryPrimeFlatFamily Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 1000000

lemma scaled_error_bound (T D H i j E : ℝ)
    (hT : 1 ≤ T) (hH : 0 ≤ H) (hD : 1024*(H+1)*T^2 ≤ D)
    (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hEsq : E^2 ≤ 32*(H+1)*(2*D*i)*(2*D*j)*(2*D*i+2*D*j+1)) :
    T*(E+12*D*i+12*D*j+8) ≤ 2*D^2*i*j := by
  have hT0 : 0 ≤ T := by linarith
  have hT2 : T ≤ T^2 := by nlinarith
  have hHprod : 0 ≤ H*T^2 := mul_nonneg hH (sq_nonneg _)
  have hD0 : 1 ≤ D := by nlinarith
  have hDT : 32*T ≤ D := by nlinarith
  have hscale : 640*(H+1)*T^2 ≤ D := by nlinarith
  have hi0 : 0 ≤ i := by linarith
  have hj0 : 0 ≤ j := by linarith
  have hij0 : 0 ≤ i*j := mul_nonneg hi0 hj0
  have hij1 : 1 ≤ i*j := by nlinarith
  have hsum : i+j ≤ 2*i*j := by nlinarith [mul_nonneg (sub_nonneg.mpr hi) (sub_nonneg.mpr hj)]
  have harg : 2*D*i+2*D*j+1 ≤ 5*D*i*j := by
    have hs := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2*D by linarith)
    have hdij := mul_le_mul_of_nonneg_left hij1 (show 0 ≤ D by linarith)
    nlinarith
  have hbound : E^2 ≤ 640*(H+1)*D^3*(i*j)^2 := by
    have hm := mul_le_mul_of_nonneg_left harg (show 0 ≤ 128*(H+1)*D^2*i*j by positivity)
    nlinarith
  have hETsq : (E*T)^2 ≤ (D^2*i*j)^2 := by
    have hm := mul_le_mul_of_nonneg_right hbound (sq_nonneg T)
    have hs := mul_le_mul_of_nonneg_right hscale (show 0 ≤ D^3*(i*j)^2 by positivity)
    nlinarith
  have hET : E*T ≤ D^2*i*j := by
    have hV : 0 ≤ D^2*i*j := by positivity
    nlinarith [sq_nonneg (E*T-D^2*i*j)]
  have hlinear : 12*D*i+12*D*j+8 ≤ 32*D*i*j := by
    have hs := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 12*D by linarith)
    have hdij := mul_le_mul_of_nonneg_left hij1 (show 0 ≤ D by linarith)
    nlinarith
  have hlinT : T*(12*D*i+12*D*j+8) ≤ D^2*i*j := by
    have hm := mul_le_mul_of_nonneg_left hlinear hT0
    have hs := mul_le_mul_of_nonneg_right hDT (show 0 ≤ D*i*j by positivity)
    nlinarith
  nlinarith

/-- Spacing and prime threshold can be selected before the prime, and all
larger odd primes work. Both sum counts and nonzero difference counts have
the specified relative error. -/
theorem every_prime_relative_family (η : ℝ) (hη : 0 < η) (H : ℕ) :
    ∃ D : ℕ, 0 < D ∧ ∀ p : ℕ, ∀ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      max (8*(D*H)+2) (2*(D*H)^2) < p →
      ∃ B : ℕ → Finset (ZMod p × ZMod p), B 0=∅ ∧ Monotone B ∧
        ∀ i ≤ H, ∀ j ≤ H,
          (∀ z, |(pairCount (B i) (B j) z : ℝ)-4*(D : ℝ)^2*i*j| ≤
            η*(4*(D : ℝ)^2*i*j)) ∧
          ∀ z, z ≠ 0 →
            |(pairCount (B i) ((B j).image Neg.neg) z : ℝ)-4*(D : ℝ)^2*i*j| ≤
              η*(4*(D : ℝ)^2*i*j) := by
  obtain ⟨T,hTbig⟩ := exists_nat_gt (max (1 : ℝ) (1/η))
  have hT : (1 : ℝ) ≤ T := (lt_of_le_of_lt (le_max_left _ _) hTbig).le
  have hηT : 1 < η*T := by
    have hh := (div_lt_iff₀ hη).mp (lt_of_le_of_lt (le_max_right _ _) hTbig)
    linarith
  let D : ℕ := 1024*(H+1)*T^2
  have hTnat : 0 < T := by exact_mod_cast (show (0 : ℝ) < T by linarith)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D,hD,fun p hp hprime ↦ ?_⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hp1 : 8*(D*H)+1 < p := by omega
  have hp2 : 2*(D*H)^2 < p := lt_of_le_of_lt (le_max_right _ _) hprime
  obtain ⟨B,hB,E,hE⟩ := every_prime_flat_family p (by omega) D H hD hp1 hp2
  let C : ℕ → Finset (ZMod p × ZMod p) := fun i ↦ if i=0 then ∅ else B i
  refine ⟨C,by simp [C],?_,?_⟩
  · intro i j hij
    by_cases hi : i=0
    · simp [C,hi]
    · have hj : j ≠ 0 := by omega
      simp only [C,if_neg hi,if_neg hj]
      exact hB hij
  · intro i hiH j hjH
    by_cases hi : i=0
    · subst i
      simp [C,pairCount]
    by_cases hj : j=0
    · subst j
      simp [C,pairCount]
    obtain ⟨he0,hesq,hes,hed⟩ := hE i (by omega) hiH j (by omega) hjH
    have hb := scaled_error_bound T D H i j (E i j) hT (Nat.cast_nonneg H)
      (by dsimp [D]; push_cast; rfl) (by exact_mod_cast (show 1 ≤ i by omega))
      (by exact_mod_cast (show 1 ≤ j by omega)) hesq
    have hfinal : E i j+12*D*i+12*D*j+8 ≤ η*(4*(D : ℝ)^2*i*j) := by
      apply le_of_mul_le_mul_left (a := (T : ℝ)) _ (by linarith)
      have hm := mul_le_mul_of_nonneg_right hηT.le (show 0 ≤ 4*(D : ℝ)^2*i*j by positivity)
      have hz : 0 ≤ (D : ℝ)^2*i*j := by positivity
      nlinarith
    simp only [C,if_neg hi,if_neg hj]
    exact ⟨fun z ↦ (hes z).trans hfinal,fun z hz ↦ (hed z hz).trans hfinal⟩

end Erdos66EveryPrimeRelativeFamily
