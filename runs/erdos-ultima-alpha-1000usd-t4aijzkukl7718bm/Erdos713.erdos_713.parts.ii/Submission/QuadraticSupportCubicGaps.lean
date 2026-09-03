import FormalConjecturesUtil
import Submission.QuadraticSupportGapObstruction

/-! Quantitative integer-secant constraints on quadratic support gaps.
These are analytic necessary conditions, not a rationality theorem. -/
open Filter Asymptotics
open scoped Topology
namespace Erdos713QuadraticSupportCubicGaps
open Erdos713ExactCloneSaturation Erdos713QuadraticSupportGapObstruction
set_option maxHeartbeats 2000000

lemma rise_forces_gap {f : ℕ → ℕ} {a b c : ℕ} {ε : ℝ}
    (hab : a < b) (hbc : b < c) (hs : QuadSupport f ε b)
    (hrise : ((f b : ℝ)-(f a : ℝ))/((b : ℝ)-(a : ℝ)) <
      ((f c : ℝ)-(f b : ℝ))/((c : ℝ)-(b : ℝ))) :
    1 ≤ ε*((b : ℝ)-(a : ℝ))*((c : ℝ)-(b : ℝ))*((c : ℝ)-(a : ℝ)) := by
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have hbcR : (b : ℝ) < c := by exact_mod_cast hbc
  have hcross := (div_lt_div_iff₀ (sub_pos.mpr habR) (sub_pos.mpr hbcR)).mp hrise
  have hi : ((f b : ℤ)-(f a : ℤ))*((c : ℤ)-(b : ℤ)) <
      ((f c : ℤ)-(f b : ℤ))*((b : ℤ)-(a : ℤ)) := by exact_mod_cast hcross
  have hiz : 1 ≤ ((f c : ℤ)-(f b : ℤ))*((b : ℤ)-(a : ℤ)) -
      ((f b : ℤ)-(f a : ℤ))*((c : ℤ)-(b : ℤ)) := by omega
  have hir : (1 : ℝ) ≤ ((f c : ℝ)-(f b : ℝ))*((b : ℝ)-(a : ℝ)) -
      ((f b : ℝ)-(f a : ℝ))*((c : ℝ)-(b : ℝ)) := by exact_mod_cast hiz
  have h1 := mul_le_mul_of_nonneg_right (hs c) (sub_nonneg.mpr habR.le)
  have h2 := mul_le_mul_of_nonneg_right (hs a) (sub_nonneg.mpr hbcR.le)
  nlinarith only [h1,h2,hir]

lemma late_rise {g : ℕ → ℝ} (ht : Tendsto g atTop atTop) (I : ℕ) :
    ∃ i : ℕ, I ≤ i ∧ g i < g (i+1) := by
  by_contra hb
  push_neg at hb
  have hbound (i : ℕ) (hi : I ≤ i) : g i ≤ g I := by
    induction i, hi using Nat.le_induction with
    | base => exact le_rfl
    | succ i hi ih => exact (hb i hi).trans ih
  obtain ⟨i,hi,hbig⟩ := ((eventually_ge_atTop I).and (ht.eventually_gt_atTop (g I))).exists
  exact (not_le_of_gt hbig) (hbound i hi)

/-- Every increasing support sequence has arbitrarily late positions at
which the curvature times the cubic gap product is at least one. -/
theorem late_gap_product {f : ℕ → ℕ} {α c : ℝ} (ha : 1 < α) (hc : 0 < c)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    {n : ℕ → ℕ} {ε : ℕ → ℝ} (hn : StrictMono n)
    (hs : ∀ i, QuadSupport f (ε i) (n i)) (I : ℕ) :
    ∃ i : ℕ, I ≤ i ∧ 1 ≤ ε (i+1)*((n (i+1) : ℝ)-(n i : ℝ))*
      ((n (i+2) : ℝ)-(n (i+1) : ℝ))*((n (i+2) : ℝ)-(n i : ℝ)) := by
  have hε (i : ℕ) : 0 ≤ ε i := (curvature_pos (by linarith) hc h (hs i)).le
  obtain ⟨i,hi,hrise⟩ := late_rise (secants_top ha hc h hn hε hs) I
  refine ⟨i,hi,?_⟩
  exact rise_forces_gap (hn (Nat.lt_succ_self i)) (hn (by omega : i+1 < i+2))
    (hs (i+1)) hrise

lemma eventually_normalized_curvature {f : ℕ → ℕ} {α c : ℝ} (hc : 0 < c)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∀ᶠ n : ℕ in atTop, ∀ ε : ℝ, QuadSupport f ε n →
      ε*(n : ℝ)^(2-α) ≤ 2*c := by
  filter_upwards [(Erdos713FutureRecords.ratio_limit h).eventually_lt_const
    (show c < 2*c by linarith), eventually_gt_atTop (0 : ℕ)] with n hn hnp
  intro ε hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnp
  have hp := Real.rpow_pos_of_pos hnR α
  have hu := (div_lt_iff₀ hp).mp hn
  have hb := hs 0
  simp only [Nat.cast_zero,zero_pow (by decide : 2 ≠ 0),zero_sub] at hb
  have hz : 0 ≤ (f 0 : ℝ) := Nat.cast_nonneg _
  have he : (n : ℝ)^(2-α)*(n : ℝ)^α = (n : ℝ)^2 := by
    rw [← Real.rpow_add hnR,sub_add_cancel,Real.rpow_two]
  apply le_of_mul_le_mul_right (a := (n : ℝ)^α) _ hp
  rw [mul_assoc,he]
  linarith

/-- A quantitative form of the support-gap obstruction. Write h,j for the
two successive gaps at the middle support order b. Arbitrarily late,
`b^(2-alpha) <= 4*c*max(h,j)^3`. No new extremal asymptotic is asserted. -/
theorem late_cubic_gap {f : ℕ → ℕ} {α c : ℝ} (ha : 1 < α) (hc : 0 < c)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    {n : ℕ → ℕ} {ε : ℕ → ℝ} (hn : StrictMono n)
    (hs : ∀ i, QuadSupport f (ε i) (n i)) (I : ℕ) :
    ∃ i : ℕ, I ≤ i ∧ (n (i+1) : ℝ)^(2-α) ≤
      4*c*(max (n (i+1)-n i) (n (i+2)-n (i+1)) : ℕ)^3 := by
  have hshift : Tendsto (fun i => n (i+1)) atTop atTop :=
    hn.tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  obtain ⟨J,hJ⟩ := eventually_atTop.mp
    (hshift.eventually (eventually_normalized_curvature hc h))
  obtain ⟨i,hi,hgap⟩ := late_gap_product ha hc h hn hs (max I J)
  have hcurv := hJ i ((le_max_right I J).trans hi) _ (hs (i+1))
  let d : ℕ := max (n (i+1)-n i) (n (i+2)-n (i+1))
  have h01 : n i < n (i+1) := hn (by omega)
  have h12 : n (i+1) < n (i+2) := hn (by omega)
  have h01R : (n i : ℝ) < n (i+1) := by exact_mod_cast h01
  have h12R : (n (i+1) : ℝ) < n (i+2) := by exact_mod_cast h12
  have hd1 : (n (i+1) : ℝ)-(n i : ℝ) ≤ d := by
    have hh : ((n (i+1)-n i : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast le_max_left _ _
    simpa only [Nat.cast_sub h01.le] using hh
  have hd2 : (n (i+2) : ℝ)-(n (i+1) : ℝ) ≤ d := by
    have hh : ((n (i+2)-n (i+1) : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast le_max_right _ _
    simpa only [Nat.cast_sub h12.le] using hh
  let P : ℝ := ((n (i+1) : ℝ)-(n i : ℝ))*
    ((n (i+2) : ℝ)-(n (i+1) : ℝ))*((n (i+2) : ℝ)-(n i : ℝ))
  have hP : 0 ≤ P := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr h01R.le) (sub_nonneg.mpr h12R.le))
    (sub_nonneg.mpr (h01R.trans h12R).le)
  have hPd : P ≤ 2*(d : ℝ)^3 := by
    calc
      _ ≤ (d : ℝ)*d*(2*d) := mul_le_mul
        (mul_le_mul hd1 hd2 (sub_nonneg.mpr h12R.le) (Nat.cast_nonneg d))
        (by linarith) (sub_nonneg.mpr (h01R.trans h12R).le) (by positivity)
      _ = _ := by ring
  have hp : 0 ≤ (n (i+1) : ℝ)^(2-α) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlo := mul_le_mul_of_nonneg_right hgap hp
  have hhi := mul_le_mul_of_nonneg_right hcurv hP
  have hd := mul_le_mul_of_nonneg_left hPd (show 0 ≤ 2*c by positivity)
  refine ⟨i,(le_max_left I J).trans hi,?_⟩
  change (n (i+1) : ℝ)^(2-α) ≤ 4*c*(d : ℝ)^3
  dsimp only [P] at hhi hd
  nlinarith only [hlo,hhi,hd]

#print axioms rise_forces_gap
#print axioms late_gap_product
#print axioms late_cubic_gap
end Erdos713QuadraticSupportCubicGaps
