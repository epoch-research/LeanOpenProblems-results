import Submission.CyclicLiftMixedExplore
import Submission.OriginRepairExplore

/-! All four mixed types of a common-source change of finite period. -/
namespace Erdos66ClippedTwoPeriod
open Erdos66CyclicLiftMixed Erdos66ClippedModulus Erdos66OuterCarryProfile
  Erdos66OuterMixedPrefix Erdos66CyclicThickening Erdos66SaturatingCyclicFamily
open scoped Classical
set_option maxHeartbeats 1800000

variable (M K L : ℕ) [NeZero M] [NeZero K] [NeZero L]

lemma repeated_clipped_cross_error (hNL : M*K ≤ L)
    (C D : Finset (ZMod L)) (η : ℝ)
    (hprefix : ∀ z u, u ≤ L →
      |(prefixCount L C D z u:ℝ)-(u:ℝ)/L*actualMean L C D| ≤ η*actualMean L C D)
    (z : ZMod (M*K)) :
    |(cyclicCount (M*K) (outerLift M K (rebase M L C)) (rebase (M*K) L D) z:ℝ)-
      (M*K:ℕ)/L*actualMean L C D| ≤ 4*K*η*actualMean L C D := by
  have hMN : M ≤ M*K := Nat.le_mul_of_pos_right M (NeZero.pos K)
  have hmain : (∑ i : Fin K, (M:ℝ)/L*actualMean L C D)=
      (M*K:ℕ)/L*actualMean L C D := by simp; ring
  have herr : (∑ i : Fin K, 4*η*actualMean L C D)=4*K*η*actualMean L C D := by simp; ring
  rw [repeated_clipped_cross_identity,Nat.cast_sum,←hmain,←herr,←Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i hi ↦
    rebase_prefix_error (M*K) L hNL C D η hprefix (z-(M*i.val:ℕ)) M hMN))

noncomputable def twoPeriod (C : Finset (ZMod L)) (side : Bool) : Finset (ZMod (M*K)) :=
  if side then rebase (M*K) L C else outerLift M K (rebase M L C)

lemma cyclicCount_comm (N : ℕ) [NeZero N] (A B : Finset (ZMod N)) (z : ZMod N) :
    cyclicCount N A B z=cyclicCount N B A z :=
  Erdos66OriginRepair.pairCount_comm A B z

lemma actualMean_comm (C D : Finset (ZMod L)) : actualMean L C D=actualMean L D C := by
  unfold actualMean
  ring

/-- Uniform estimates about the same source-cardinality mean for both
self types and both orientations of the mixed type. -/
theorem twoPeriod_error (hNL : M*K ≤ L) (C D : Finset (ZMod L))
    (η : ℝ) (hη : 0 ≤ η)
    (hCD : ∀ z u, u ≤ L →
      |(prefixCount L C D z u:ℝ)-(u:ℝ)/L*actualMean L C D| ≤ η*actualMean L C D)
    (hDC : ∀ z u, u ≤ L →
      |(prefixCount L D C z u:ℝ)-(u:ℝ)/L*actualMean L D C| ≤ η*actualMean L D C)
    (b d : Bool) (z : ZMod (M*K)) :
    |(cyclicCount (M*K) (twoPeriod M K L C b) (twoPeriod M K L D d) z:ℝ)-
      (M*K:ℕ)/L*actualMean L C D| ≤ 4*K*η*actualMean L C D := by
  have hMN : M ≤ M*K := Nat.le_mul_of_pos_right M (NeZero.pos K)
  cases b <;> cases d <;> simp only [twoPeriod,Bool.false_eq_true,if_false,if_true]
  · rw [outer_cyclicCount]
    simp only [Nat.cast_mul]
    have hh := rebase_cyclic_error M L (hMN.trans hNL) C D η hCD (reduceDigit M K z)
    have hs := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg K (α:=ℝ))
    have he : (K:ℝ)*(cyclicCount M (rebase M L C) (rebase M L D) (reduceDigit M K z):ℝ)-
        (M:ℝ)*K/L*actualMean L C D = K*((cyclicCount M (rebase M L C) (rebase M L D)
        (reduceDigit M K z):ℝ)-(M:ℝ)/L*actualMean L C D) := by ring
    rw [he,abs_mul,abs_of_nonneg (Nat.cast_nonneg K)]
    nlinarith only [hs]
  · exact repeated_clipped_cross_error M K L hNL C D η hCD z
  · rw [cyclicCount_comm,actualMean_comm L C D]
    exact repeated_clipped_cross_error M K L hNL D C η hDC z
  · have hh := rebase_cyclic_error (M*K) L hNL C D η hCD z
    have hK : (1:ℝ) ≤ K := by exact_mod_cast NeZero.pos K
    have hm := actualMean_nonneg L C D
    have hs := mul_le_mul_of_nonneg_right hK (show 0 ≤ 4*η*actualMean L C D by positivity)
    exact hh.trans (by nlinarith only [hs])

/-- Actual-mean normalization, uniform in the two period choices. -/
theorem twoPeriod_actual_error (hNL : M*K ≤ L) (hLN : L ≤ 2*(M*K))
    (C D : Finset (ZMod L)) (η : ℝ) (hη : 0 ≤ η) (hηK : 16*K*η ≤ 1)
    (hCD : ∀ z u, u ≤ L →
      |(prefixCount L C D z u:ℝ)-(u:ℝ)/L*actualMean L C D| ≤ η*actualMean L C D)
    (hDC : ∀ z u, u ≤ L →
      |(prefixCount L D C z u:ℝ)-(u:ℝ)/L*actualMean L D C| ≤ η*actualMean L D C)
    (b d : Bool) (z : ZMod (M*K)) :
    |(cyclicCount (M*K) (twoPeriod M K L C b) (twoPeriod M K L D d) z:ℝ)-
      actualMean (M*K) (twoPeriod M K L C b) (twoPeriod M K L D d)| ≤
      32*K*η*actualMean (M*K) (twoPeriod M K L C b) (twoPeriod M K L D d) := by
  have hl : (0:ℝ)<L := by exact_mod_cast NeZero.pos L
  have hhalf : (1:ℝ)/2 ≤ (M*K:ℕ)/L := by
    apply (le_div_iff₀ hl).mpr
    have hh : (L:ℝ) ≤ 2*(M*K:ℕ) := by exact_mod_cast hLN
    linarith
  have hnom : ∀ z : ZMod (M*K),
      |(cyclicCount (M*K) (twoPeriod M K L C b) (twoPeriod M K L D d) z:ℝ)-
        (M*K:ℕ)/L*actualMean L C D| ≤
        (8*K*η)*((M*K:ℕ)/L*actualMean L C D) := by
    intro z
    have hh := twoPeriod_error M K L hNL C D η hη hCD hDC b d z
    have hs := mul_le_mul_of_nonneg_right hhalf
      (show 0 ≤ (8*K*η)*actualMean L C D by positivity [actualMean_nonneg L C D])
    exact hh.trans (by nlinarith only [hs])
  have hh := normalize_to_actualMean (M*K) _ _ ((M*K:ℕ)/L*actualMean L C D)
    (8*K*η) (by positivity [actualMean_nonneg L C D]) (by positivity)
    (by nlinarith only [hηK]) hnom z
  convert hh using 1 <;> ring

lemma twoPeriod_prefix_agree (C : Finset (ZMod L)) (b d : Bool)
    (a : ℕ) (ha : a<M) :
    (a : ZMod (M*K))∈twoPeriod M K L C b ↔
      (a : ZMod (M*K))∈twoPeriod M K L C d := by
  have hh := repeated_clipped_prefix_agree M K L C a ha
  cases b <;> cases d <;> simp only [twoPeriod,Bool.false_eq_true,if_false,if_true]
  · exact hh
  · exact hh.symm

end Erdos66ClippedTwoPeriod
