import Submission.ReflectionRoundingPatchExplore

/-! A pointwise lower bound for the harmonic fractional profile, and a
consequent gap bound for any bounded-prefix-discrepancy rounding. -/
namespace Erdos66ProfileLowerGap
open AdditiveCombinatorics Erdos66Fractional Erdos66ReflectionRoundingPatch
  Erdos66Counting Erdos66Rounding Erdos66Generating
open scoped Classical
set_option maxHeartbeats 1800000

lemma profile_square_lower (n : ℕ) : 1/((n:ℝ)+1) ≤ (profile n)^2 := by
  let S := ∑ i∈Finset.range (n+1), stepMass i
  have hconv := cumulative_convolution_bound stepMass stepMass_zero stepMass_nonneg n
  have hsub : (∑ i∈Finset.range n, stepMass i) ≤ S :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun i _ _ ↦ stepMass_nonneg i)
  have hnon : 0 ≤ ∑ i∈Finset.range n, stepMass i := Finset.sum_nonneg (fun i _ ↦ stepMass_nonneg i)
  have hnonS : 0 ≤ S := hnon.trans hsub
  have hsq : (∑ i∈Finset.range n, stepMass i)^2 ≤ S^2 :=
    pow_le_pow_left₀ hnon hsub 2
  have he : 2*S=1-1/((n:ℝ)+1)+∑ i∈Finset.range (n+1), sumConv stepMass stepMass i := by
    dsimp only [S]
    rw [Finset.mul_sum]
    simp_rw [stepMass_recurrence]
    rw [Finset.sum_add_distrib,kernelCoeff_partial]
  change 1/((n:ℝ)+1) ≤ (1-S)^2
  nlinarith

lemma sqrt_mul_profile_lower (n : ℕ) : 1 ≤ Real.sqrt ((n:ℝ)+1)*profile n := by
  have hs := profile_square_lower n
  have hn : 0<(n:ℝ)+1 := by positivity
  have hh := (div_le_iff₀ hn).mp hs
  have hsqrt := Real.sq_sqrt hn.le
  have hp := profile_nonneg n
  have hsn := Real.sqrt_nonneg ((n:ℝ)+1)
  have he : (Real.sqrt ((n:ℝ)+1)*profile n)^2=((n:ℝ)+1)*(profile n)^2 := by
    rw [mul_pow,hsqrt]
  have hprod := mul_nonneg hsn hp
  nlinarith

lemma profile_pos (n : ℕ) : 0<profile n := by
  have hh := sqrt_mul_profile_lower n
  have hs := Real.sqrt_nonneg ((n:ℝ)+1)
  have hp := profile_nonneg n
  by_contra hn
  have he : profile n=0 := le_antisymm (not_lt.mp hn) hp
  rw [he,mul_zero] at hh
  norm_num at hh

lemma interval_nonempty_of_mass (A : Set ℕ) (p : ℕ → ℝ) (D : ℝ)
    (hA : ∀ N, |(count A N:ℝ)-cumulative p N| ≤ D) (a w : ℕ) (v : ℝ)
    (hv : ∀ i∈Finset.Ico a (a+w), v ≤ p i) (hmass : 2*D<(w:ℝ)*v) :
    (intervalPart A a (a+w)).Nonempty := by
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  have hh := local_count_error A p D hA a (a+w) (by omega)
  rw [he,Finset.card_empty,Nat.cast_zero,zero_sub,abs_neg] at hh
  have hsum := Finset.sum_le_sum hv
  simp only [Finset.sum_const,Nat.card_Ico,Nat.add_sub_cancel_left,nsmul_eq_mul] at hsum
  have hb := (le_abs_self (∑ i∈Finset.Ico a (a+w), p i)).trans hh
  linarith

lemma interval_nonempty_of_length (A : Set ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hA : ∀ N, |(count A N:ℝ)-cumulative profile N| ≤ D)
    (a w : ℕ) (hlen : 2*D*Real.sqrt ((a+w:ℕ):ℝ) < w) :
    (intervalPart A a (a+w)).Nonempty := by
  have hw : 0<w := by
    have hh := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) hD) (Real.sqrt_nonneg ((a+w:ℕ):ℝ))
    have hw' : (0:ℝ)<w := hh.trans_lt hlen
    exact_mod_cast hw'
  have he : (a+w-1:ℕ)+1=a+w := by omega
  have hprofile := sqrt_mul_profile_lower (a+w-1)
  have heR : ((a+w-1:ℕ):ℝ)+1=((a+w:ℕ):ℝ) := by exact_mod_cast he
  rw [heR] at hprofile
  apply interval_nonempty_of_mass A profile D hA a w (profile (a+w-1))
  · intro i hi
    exact profile_antitone (by have := (Finset.mem_Ico.mp hi).2; omega)
  · have hp := profile_pos (a+w-1)
    have h1 := mul_lt_mul_of_pos_right hlen hp
    have h2 := mul_le_mul_of_nonneg_left hprofile (mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) hD)
    nlinarith

end Erdos66ProfileLowerGap
