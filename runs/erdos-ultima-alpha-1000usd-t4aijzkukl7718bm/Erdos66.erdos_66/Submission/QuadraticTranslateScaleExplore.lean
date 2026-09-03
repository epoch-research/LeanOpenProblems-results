import Submission.QuadraticTranslateAnchorExplore
import Submission.InterceptSelectionScaleExplore

/-! The collision-free quadratic-translate estimate is relatively small at
full-prefix witness density. Its full lift still has the wrong mass for an
infinite natural-number construction. These facts do not settle Erdős 66. -/
namespace Erdos66QuadraticTranslateScale
open Erdos66QuadraticTranslateAnchor Erdos66Counting Erdos66TauberianProfile
  Erdos66InterceptSelectionScale Erdos66FullFaithfulLiftObstruction
  Erdos66FaithfulParabolaCardinality Erdos66PrefixFaithfulParabolaLift
  Erdos66QuadraticPrefixMass Erdos66OriginRepair
open Filter AdditiveCombinatorics
open scoped Classical Topology
set_option maxHeartbeats 1800000

lemma cutoff_div_count_square_limit {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ ↦ (N : ℝ)/(count A N : ℝ)^2) atTop (𝓝 0) := by
  have hd : 0<4*c/Real.pi := by have := Erdos66Explore.limit_pos hc ht; positivity
  have hlog : Tendsto (fun N : ℕ ↦ Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := (hlog.const_div_atTop (1 : ℝ)).div
    (witness_counting_square_profile hc ht) hd.ne'
  simp only [zero_div] at hh
  apply hh.congr'
  filter_upwards [count_square_eventually_gt_cutoff hc ht,eventually_ge_atTop 2] with N hcount hN
  have hn : (N : ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have hl : Real.log (N : ℝ)≠0 :=
    (Real.log_pos (by exact_mod_cast (show 1<N by omega))).ne'
  have hcN : (count A N : ℝ)≠0 := by
    have : count A N≠0 := by intro he; simp [he] at hcount
    exact_mod_cast this
  dsimp only [Pi.div_apply]
  field_simp

lemma sqrt_cutoff_div_count_limit {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ ↦ Real.sqrt N/(count A N : ℝ)) atTop (𝓝 0) := by
  have hh := (cutoff_div_count_square_limit hc ht).sqrt
  simpa only [Real.sqrt_zero,Real.sqrt_div (Nat.cast_nonneg _),
    Real.sqrt_sq (Nat.cast_nonneg _)] using hh

/-- At full-prefix density, all complete plane counts of this explicit lift
are relatively accurate, with one lift preceding every target. -/
theorem prime_prefix_lift_relative_error {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c))
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      ∀ z : ZMod p × ZMod p,
        |(pairCount (lift (prefixParameters A p)) (lift (prefixParameters A p)) z : ℝ)-
          (count A p : ℝ)^2| ≤ ε*(count A p : ℝ)^2 := by
  have he := (sqrt_cutoff_div_count_limit hc ht).eventually_lt_const hε
  filter_upwards [he,count_square_eventually_gt_cutoff hc ht,eventually_ge_atTop 3]
    with p hbound hcount hp3
  intro hp
  letI : Fact p.Prime := ⟨hp⟩
  intro z
  have hF : ringChar (ZMod p)≠2 := by simpa only [ZMod.ringChar_zmod_n] using (show p≠2 by omega)
  have hC : (0 : ℝ)<count A p := by
    have : 0<count A p := by nlinarith
    exact_mod_cast this
  have hh := lift_self_abs_error hF (prefixParameters A p) z
  rw [prefixParameters_card,ZMod.card] at hh
  have he' := (div_lt_iff₀ hC).mp hbound
  have hm := mul_lt_mul_of_pos_right he' hC
  exact hh.trans (by nlinarith only [hm])

lemma full_quadratic_lift_forces_mass (A : Set ℕ) (p : ℕ) [Fact p.Prime]
    (hsub : ∀ n∈encodePlane p (lift (prefixParameters A p)), n∈A) :
    p*count A p ≤ count A (p^2) := by
  have hinc : encodePlane p (lift (prefixParameters A p)) ⊆ cutoff A (p^2) := by
    intro n hn
    exact mem_cutoff.mpr ⟨encodePlane_lt p _ hn,hsub n hn⟩
  have hcard := Finset.card_le_card hinc
  rw [encodePlane_card,lift_card,prefixParameters_card,ZMod.card] at hcard
  simpa only [count,Nat.mul_comm] using hcard

/-- Good complete field counts do not justify retaining the entire lift:
its exact cardinality is already too large for a hypothetical witness. -/
theorem eventually_no_full_quadratic_lift {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n : ℝ)/Real.log n) atTop (𝓝 c)) :
    ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime,
      letI : Fact p.Prime := ⟨hp⟩
      ¬ (∀ n∈encodePlane p (lift (prefixParameters A p)), n∈A) := by
  filter_upwards [eventual_no_linear_mass_amplification hc ht] with p hmass
  intro hp
  letI : Fact p.Prime := ⟨hp⟩
  intro hsub
  have hm := full_quadratic_lift_forces_mass A p hsub
  have hle : (p-1)*count A p ≤ p*count A p := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  omega

end Erdos66QuadraticTranslateScale
