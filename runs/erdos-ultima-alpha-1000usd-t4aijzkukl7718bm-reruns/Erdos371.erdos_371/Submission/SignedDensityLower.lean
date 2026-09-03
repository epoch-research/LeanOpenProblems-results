import FormalConjecturesUtil
import Submission.SelbergSeparation
import Submission.HeightBalance

/-! An unconditional positive lower-density bound for both orientations.
The value one half, and even existence of the two densities, remain open here. -/

namespace Erdos371SignedDensityLower

open Finset Filter Erdos371PrimeDiscrepancy Erdos371RectangleSeparation
  Erdos371SelbergSeparation
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def logHeight (n : ℕ) : ℝ := Nat.log 2 (P n)
def up (n : ℕ) : Prop := P n < P (n+1)
noncomputable def upCount (N : ℕ) : ℕ := ((range N).filter up).card
noncomputable def downCount (N : ℕ) : ℕ := ((range N).filter fun n => ¬up n).card
noncomputable def far (L n : ℕ) : Prop := n ≠ 0 ∧
  2^L*min (P n) (P (n+1)) < max (P n) (P (n+1))
noncomputable def farCount (L N : ℕ) : ℕ := ((range N).filter (far L)).card

lemma logHeight_nonneg (n : ℕ) : 0 ≤ logHeight n := Nat.cast_nonneg _

lemma logHeight_bound {n t : ℕ} (hn : n ≤ 2^t) : logHeight n ≤ (t:ℝ) := by
  apply Nat.cast_le.mpr
  have hh := Nat.log_mono_right (b := 2) (Nat.maxPrimeFac_le.trans hn)
  simpa only [Nat.log_pow (by decide : 1<(2:ℕ))] using hh

lemma log_gap {a b L : ℕ} (ha : 0 < a) (h : 2^L*a < b) :
    Nat.log 2 a+L ≤ Nat.log 2 b := by
  apply Nat.le_log_of_pow_le (by decide)
  calc
    2^(Nat.log 2 a+L) = 2^L*2^(Nat.log 2 a) := by rw [pow_add, mul_comm]
    _ ≤ 2^L*a := Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ ha.ne')
    _ ≤ b := h.le

lemma primefac_pos {n : ℕ} (hn : 0 < n) : 0 < P n := by
  by_cases he : n=1
  · simp [he,P]
  · exact (Nat.prime_maxPrimeFac_of_one_lt n (by omega)).pos

lemma logHeight_far {L n : ℕ} (hn : far L n) : (L:ℝ) ≤ |logHeight (n+1)-logHeight n| := by
  obtain ⟨hn0,hfar⟩ := hn
  by_cases hu : up n
  · have h := log_gap (primefac_pos (by omega : 0<n))
      (show 2^L*P n < P (n+1) by simpa [max_eq_right hu.le,min_eq_left hu.le] using hfar)
    have hh : logHeight n+(L:ℝ) ≤ logHeight (n+1) := by dsimp [logHeight]; exact_mod_cast h
    linarith [le_abs_self (logHeight (n+1)-logHeight n)]
  · have hle : P (n+1) ≤ P n := le_of_not_gt hu
    have h := log_gap (primefac_pos (by omega : 0<n+1))
      (show 2^L*P (n+1) < P n by simpa [max_eq_left hle,min_eq_right hle] using hfar)
    have hh : logHeight (n+1)+(L:ℝ) ≤ logHeight n := by dsimp [logHeight]; exact_mod_cast h
    have hab := neg_le_abs (logHeight (n+1)-logHeight n)
    linarith

lemma farCount_bound (L N : ℕ) : N ≤ farCount L N+(closeInputs L N).card+1 := by
  have hsub : range N ⊆ ((range N).filter (far L)) ∪ closeInputs L N ∪ {0} := by
    intro n hn
    by_cases hn0 : n=0
    · exact mem_union_right _ (mem_singleton.mpr hn0)
    · by_cases hc : max (P n) (P (n+1)) ≤ 2^L*min (P n) (P (n+1))
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hn,hc⟩))
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hn,hn0,not_le.mp hc⟩))
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  have hh' := card_union_le ((range N).filter (far L)) (closeInputs L N)
  simp only [card_range, card_singleton] at hh
  unfold farCount
  omega

lemma finite_two_sides (t L : ℕ) :
    (L:ℝ)*((2:ℝ)^t-(closeInputs L (2^t)).card-1) ≤
      (t+L:ℕ)*upCount (2^t)+(t:ℝ) ∧
    (L:ℝ)*((2:ℝ)^t-(closeInputs L (2^t)).card-1) ≤
      (t+L:ℕ)*downCount (2^t)+(t:ℝ) := by
  have hh := Erdos371HeightBalance.two_sides logHeight up (far L) (2^t)
    (H := (t:ℝ)) (L := (L:ℝ)) (Nat.cast_nonneg _) (by
      intro n hn
      have ha := logHeight_bound (t := t) hn.le
      have hb := logHeight_bound (t := t) (by omega : n+1≤2^t)
      exact abs_le.mpr ⟨by linarith [logHeight_nonneg (n+1)], by linarith [logHeight_nonneg n]⟩)
    (by
      intro n hn
      constructor
      · intro hu
        have he : logHeight n ≤ logHeight (n+1) := Nat.cast_le.mpr (Nat.log_mono_right hu.le)
        linarith
      · intro hu
        have he : logHeight (n+1) ≤ logHeight n := Nat.cast_le.mpr (Nat.log_mono_right (le_of_not_gt hu))
        linarith)
    (fun n _ hf => logHeight_far hf)
    (by
      have h0 : logHeight 0 = 0 := by simp [logHeight,P]
      rw [h0,sub_zero,abs_of_nonneg (logHeight_nonneg _)]
      exact logHeight_bound le_rfl)
  have hc := Nat.cast_le (α := ℝ) |>.mpr (farCount_bound L (2^t))
  push_cast at hc
  have hl : (L:ℝ)*((2:ℝ)^t-(closeInputs L (2^t)).card-1) ≤ (L:ℝ)*farCount L (2^t) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    linarith
  change _ ≤ ((t:ℝ)+L)*upCount (2^t)+t ∧ _ ≤ ((t:ℝ)+L)*downCount (2^t)+t at hh
  constructor
  · simpa only [Nat.cast_add] using hl.trans hh.1
  · simpa only [Nat.cast_add] using hl.trans hh.2

lemma count_lower_algebra {Q t L : ℕ} {N C U : ℝ}
    (hQ : 0 < Q) (ht : 0 < t) (hL : L ≤ t) (htL : t ≤ 2*Q*L)
    (hN : 8*(Q:ℝ)+4 ≤ N) (hC : C ≤ N/2) (hU : 0 ≤ U)
    (h : (L:ℝ)*(N-C-1) ≤ (t+L:ℕ)*U+(t:ℝ)) :
    N/(16*(Q:ℝ)) ≤ U := by
  have hQ0 : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have ht0 : (0:ℝ) < t := Nat.cast_pos.mpr ht
  have hL' : (L:ℝ) ≤ t := Nat.cast_le.mpr hL
  have htL' : (t:ℝ) ≤ 2*(Q:ℝ)*L := by dsimp [logHeight]; exact_mod_cast htL
  have hN0 : 0 ≤ N/2-1 := by linarith
  have h1 : (L:ℝ)*(N/2-1) ≤ 2*(t:ℝ)*U+(t:ℝ) := by
    have hc := mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg (α := ℝ) L)
    have hu := mul_le_mul_of_nonneg_right hL' hU
    push_cast at h
    nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 2*Q by positivity)
  have h3 := mul_le_mul_of_nonneg_right htL' hN0
  have h4 : (t:ℝ)*(N/2-1) ≤ (t:ℝ)*(4*(Q:ℝ)*U+2*(Q:ℝ)) := by nlinarith
  have h5 := (mul_le_mul_iff_right₀ ht0).mp h4
  apply (div_le_iff₀ (by positivity : (0:ℝ)<16*Q)).mpr
  nlinarith

/-- Both orientations have a uniformly positive proportion on large dyadic
intervals. This is weaker than the conjectured one-half asymptotic. -/
theorem dyadic_positive_proportions : ∃ Q : ℕ, 0 < Q ∧ ∀ᶠ t : ℕ in atTop,
    (2:ℝ)^t/(16*(Q:ℝ)) ≤ upCount (2^t) ∧
    (2:ℝ)^t/(16*(Q:ℝ)) ≤ downCount (2^t) := by
  obtain ⟨Q,hQ,hwindow⟩ := exists_fixed_window
  have hQ0 : 0 < Q := by omega
  have hpow : Tendsto (fun t : ℕ => (2:ℝ)^t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  refine ⟨Q,hQ0,?_⟩
  filter_upwards [hwindow, hpow.eventually_ge_atTop (8*(Q:ℝ)+4), eventually_gt_atTop 0] with t ht hN ht0
  have hL : t/Q ≤ t := Nat.div_le_self _ _
  have htL : t ≤ 2*Q*(t/Q) := by
    have hh := Nat.lt_mul_div_succ t hQ0
    nlinarith [ht.1]
  have hb := finite_two_sides t (t/Q)
  exact ⟨count_lower_algebra hQ0 ht0 hL htL hN ht.2 (Nat.cast_nonneg _) hb.1,
    count_lower_algebra hQ0 ht0 hL htL hN ht.2 (Nat.cast_nonneg _) hb.2⟩

lemma upCount_mono : Monotone upCount := by
  intro N M hNM
  exact card_le_card (filter_subset_filter _ (range_mono hNM))

lemma downCount_mono : Monotone downCount := by
  intro N M hNM
  exact card_le_card (filter_subset_filter _ (range_mono hNM))

/-- Both sets of orientations have a positive lower natural density. This
asserts neither that their densities exist nor that they equal one half. -/
theorem positive_lower_proportions : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
    c ≤ (upCount N:ℝ)/N ∧ c ≤ (downCount N:ℝ)/N := by
  obtain ⟨Q,hQ,hdyad⟩ := dyadic_positive_proportions
  obtain ⟨t0,ht0⟩ := eventually_atTop.mp hdyad
  have hQ0 : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  refine ⟨1/(32*(Q:ℝ)), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2^t0), eventually_gt_atTop 0] with N hN ht
  let k := Nat.log 2 N
  have hk : t0 ≤ k := Nat.le_log_of_pow_le (by decide) hN
  have hNk : 2^k ≤ N := Nat.pow_log_le_self _ ht.ne'
  have hNhi : (N:ℝ) ≤ 2*(2:ℝ)^k := by
    have hh := (Nat.lt_pow_succ_log_self (by decide : 1<(2:ℕ)) N).le
    simpa only [pow_succ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm] using
      (Nat.cast_le (α := ℝ) |>.mpr hh)
  have hn0 : (0:ℝ) < N := Nat.cast_pos.mpr ht
  have hscale : (N:ℝ)/(32*(Q:ℝ)) ≤ (2:ℝ)^k/(16*(Q:ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hu : (N:ℝ)/(32*(Q:ℝ)) ≤ upCount N :=
    (hscale.trans (ht0 k hk).1).trans (Nat.cast_le.mpr (upCount_mono hNk))
  have hd : (N:ℝ)/(32*(Q:ℝ)) ≤ downCount N :=
    (hscale.trans (ht0 k hk).2).trans (Nat.cast_le.mpr (downCount_mono hNk))
  have he : 1/(32*(Q:ℝ)) = ((N:ℝ)/(32*(Q:ℝ)))/N := by field_simp
  rw [he]
  exact ⟨div_le_div_of_nonneg_right hu hn0.le, div_le_div_of_nonneg_right hd hn0.le⟩

lemma downCount_eq (N : ℕ) : downCount N =
    ((range N).filter fun n => P (n+1) < P n).card := by
  unfold downCount
  congr 1
  apply filter_congr
  intro n hn
  have hh := consecutive_ne n
  unfold up
  omega

lemma upCount_density (N : ℕ) : (upCount N:ℝ)/N =
    {n | P n < P (n+1)}.partialDensity Set.univ N := by
  rw [Erdos371ReflectionRange.partialDensity_eq_filter_card]
  unfold upCount up
  congr 2

lemma downCount_density (N : ℕ) : (downCount N:ℝ)/N =
    {n | P (n+1) < P n}.partialDensity Set.univ N := by
  rw [downCount_eq,Erdos371ReflectionRange.partialDensity_eq_filter_card]
  congr 2
  apply congrArg Finset.card
  ext n
  simp

/-- An unconditional lower-density result for the actual two orientations. -/
theorem two_orientations_positive_lower_density : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
    c ≤ {n | P n < P (n+1)}.partialDensity Set.univ N ∧
    c ≤ {n | P (n+1) < P n}.partialDensity Set.univ N := by
  obtain ⟨c,hc,h⟩ := positive_lower_proportions
  refine ⟨c,hc,?_⟩
  filter_upwards [h] with N hN
  simpa only [upCount_density,downCount_density] using hN

lemma count_partition (N : ℕ) : upCount N+downCount N=N := by
  simpa only [upCount,downCount,card_range] using card_filter_add_card_filter_not (s := range N) up

/-- The discrepancy stays uniformly away from the two trivial extreme values.
Convergence to zero is a substantially stronger statement and is not proved. -/
theorem signed_mean_away_from_extremes : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
    |(total N:ℝ)/N| ≤ 1-δ := by
  obtain ⟨c,hc,h⟩ := positive_lower_proportions
  refine ⟨2*c,by positivity,?_⟩
  filter_upwards [h,eventually_gt_atTop 0] with N hN hpos
  have hn0 : (0:ℝ)<N := Nat.cast_pos.mpr hpos
  have hcount : (upCount N:ℝ)+(downCount N:ℝ)=N := by exact_mod_cast count_partition N
  have htotal : (total N:ℝ)=2*(upCount N:ℝ)-N := by
    calc
      _ = 2*((((range N).filter fun n => P n < P (n+1)).card):ℝ)-N := by
        exact_mod_cast total_eq_count N
      _ = _ := by
        unfold upCount up
        congr 3
        apply congrArg Finset.card
        ext n
        simp
  have hratio : (upCount N:ℝ)/N+(downCount N:ℝ)/N=1 := by rw [← add_div,hcount,div_self hn0.ne']
  rw [htotal,sub_div,mul_div_assoc,div_self hn0.ne',abs_le]
  constructor <;> linarith [hN.1,hN.2]

end Erdos371SignedDensityLower

#print axioms Erdos371SignedDensityLower.dyadic_positive_proportions

#print axioms Erdos371SignedDensityLower.positive_lower_proportions

#print axioms Erdos371SignedDensityLower.two_orientations_positive_lower_density
#print axioms Erdos371SignedDensityLower.signed_mean_away_from_extremes
