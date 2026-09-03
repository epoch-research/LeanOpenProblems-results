import Submission.RotationMassLogBoundExplore
import Submission.DiscreteRotationBridgeExplore

/-! Expected-mass-sensitive discrepancy for the same explicit finite phase.
The modulus and phase do not depend on the eventual interval or target. -/
namespace Erdos66DiscreteRotationMass
open Erdos66RotationMassLogBound Erdos66DiscreteRotationBridge
  Erdos66ShortOrbitCarry Erdos66RotationFloorPerturbation
open Filter
open scoped Classical Topology
set_option maxHeartbeats 1600000

variable (M : ℕ) [NeZero M]

lemma phase_interval_mass_error (Q t l u : ℕ) (hQ : Q^2≤M) (ht : t<M)
    (hu : u≤Q) (a : ZMod M) :
    |(∑ k ∈ Finset.Ico l u, hit M (phase M) a t k)-
      ((u-l : ℕ) : ℝ)*((t+1 : ℕ) : ℝ)/M| ≤
      30+50*Real.log (((u-l : ℕ) : ℝ)*((t+1 : ℕ) : ℝ)/M+1) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp_rw [hit_add]
  rw [phase,hit_range_eq_rotationSum M (phaseInteger M) _ t (u-l) ht]
  have hNQ : u-l≤Q := (Nat.sub_le u l).trans hu
  have he := rotation_mass_log_bound (((phaseInteger M : ℤ) : ℝ)/M) Q
    (slope_near M Q hQ) (u-l) hNQ
    (((((phaseInteger M : ZMod M))*(l : ZMod M)+a).val : ℝ)/M)
    (((t+1 : ℕ) : ℝ)/M) (by positivity)
  simpa only [mul_div_assoc] using he

/-- The old IntervalBound interface now has an error controlled by Q*rho,
rather than Q. Every active subinterval uses the same fixed phase. -/
theorem phase_mass_intervalBound (Q t : ℕ) (hQ : Q^2≤M) (ht : t<M) :
    IntervalBound M (phase M) Q t
      (30+50*Real.log ((Q : ℝ)*((t+1 : ℕ) : ℝ)/M+1)) := by
  intro a l u _ hu
  have he := phase_interval_mass_error M Q t l u hQ ht hu a
  have hNQ : ((u-l : ℕ) : ℝ)≤Q := by exact_mod_cast (Nat.sub_le u l).trans hu
  have hm := mul_le_mul_of_nonneg_right hNQ
    (show (0 : ℝ)≤((t+1 : ℕ) : ℝ)/M by positivity)
  have hl := Real.log_le_log (show 0<((u-l : ℕ) : ℝ)*((t+1 : ℕ) : ℝ)/M+1 by positivity)
    (show ((u-l : ℕ) : ℝ)*((t+1 : ℕ) : ℝ)/M+1 ≤
      (Q : ℝ)*((t+1 : ℕ) : ℝ)/M+1 by
        simp only [mul_div_assoc] at *
        linarith only [hm])
  exact he.trans (by linarith)

/-- A complementary endpoint interval gives the same discrepancy, so the
smaller of its two expected masses suffices for a uniform interval bound. -/
theorem phase_balanced_intervalBound (Q t : ℕ) (hQ : Q^2≤M) (ht : t<M) :
    IntervalBound M (phase M) Q t
      (30+50*Real.log ((Q : ℝ)*
        min (((t+1 : ℕ) : ℝ)/M) (1-((t+1 : ℕ) : ℝ)/M)+1)) := by
  intro a l u _ hu
  rw [Finset.sum_Ico_eq_sum_range]
  simp_rw [hit_add]
  rw [phase,hit_range_eq_rotationSum M (phaseInteger M) _ t (u-l) ht]
  have hNQ : u-l≤Q := (Nat.sub_le u l).trans hu
  have hM : (0 : ℝ)<M := by exact_mod_cast NeZero.pos M
  have hρ0 : (0 : ℝ)≤((t+1 : ℕ) : ℝ)/M := by positivity
  have hρ1 : ((t+1 : ℕ) : ℝ)/M≤1 :=
    (div_le_one hM).mpr (by exact_mod_cast Nat.succ_le_iff.mpr ht)
  have he := rotation_balanced_mass_log_bound (((phaseInteger M : ℤ) : ℝ)/M) Q
    (slope_near M Q hQ) (u-l) hNQ
    (((((phaseInteger M : ZMod M))*(l : ZMod M)+a).val : ℝ)/M)
    (((t+1 : ℕ) : ℝ)/M) hρ0 hρ1
  have hm0 : (0 : ℝ)≤ min (((t+1 : ℕ) : ℝ)/M) (1-((t+1 : ℕ) : ℝ)/M) :=
    le_min hρ0 (sub_nonneg.mpr hρ1)
  have hmul := mul_le_mul_of_nonneg_right
    (show ((u-l : ℕ) : ℝ)≤Q by exact_mod_cast hNQ) hm0
  have hlog := Real.log_le_log
    (show 0<((u-l : ℕ) : ℝ)*min (((t+1 : ℕ) : ℝ)/M) (1-((t+1 : ℕ) : ℝ)/M)+1 by positivity)
    (add_le_add hmul (le_refl 1))
  have hfinal := he.trans (show 30+50*Real.log (((u-l : ℕ) : ℝ)*
      min (((t+1 : ℕ) : ℝ)/M) (1-((t+1 : ℕ) : ℝ)/M)+1) ≤
      30+50*Real.log ((Q : ℝ)*min (((t+1 : ℕ) : ℝ)/M) (1-((t+1 : ℕ) : ℝ)/M)+1) by
    linarith)
  simpa only [mul_div_assoc] using hfinal

omit [NeZero M] in
lemma mass_error_ratio_limit :
    Tendsto (fun X : ℝ ↦ (30+50*Real.log (X+1))/X) atTop (𝓝 0) := by
  have hshift : Tendsto (fun X : ℝ ↦ X+1) atTop atTop :=
    tendsto_id.atTop_add tendsto_const_nhds
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hshift
  have hinv := (tendsto_id : Tendsto (fun X : ℝ ↦ X) atTop atTop).const_div_atTop 1
  have hratio := (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1)).add hinv
  have hprod := hlog.mul hratio
  have hconst := (tendsto_id : Tendsto (fun X : ℝ ↦ X) atTop atTop).const_div_atTop 30
  have hh := hconst.add (hprod.const_mul 50)
  norm_num only [zero_mul,mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  have hx : X≠0 := by linarith
  have hx1 : X+1≠0 := by linarith
  dsimp
  field_simp

omit [NeZero M] in
lemma exists_mass_error_threshold (ε : ℝ) (hε : 0<ε) :
    ∃ T : ℝ, 0<T ∧ ∀ X : ℝ, T≤X → 30+50*Real.log (X+1)≤ε*X := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp (mass_error_ratio_limit.eventually_le_const hε)
  refine ⟨max T 1,lt_of_lt_of_le (by norm_num) (le_max_right _ _),?_⟩
  intro X hX
  have hx : 0<X := lt_of_lt_of_le (by norm_num) ((le_max_right T 1).trans hX)
  exact (div_le_iff₀ hx).mp (hT X ((le_max_left _ _).trans hX))

/-- One threshold depends only on epsilon, before every modulus, interval,
and target. Relative discrepancy tends to zero whenever expected hits grow. -/
theorem exists_uniform_relative_mass_threshold (ε : ℝ) (hε : 0<ε) :
    ∃ T : ℝ, 0<T ∧ ∀ (M : ℕ) [NeZero M] (Q t l u : ℕ),
      Q^2≤M → t<M → u≤Q →
      T≤((u-l : ℕ) : ℝ)*((t+1 : ℕ) : ℝ)/M →
      ∀ a : ZMod M,
        |(∑ k ∈ Finset.Ico l u, hit M (phase M) a t k)-
          ((u-l : ℕ) : ℝ)*((t+1 : ℕ) : ℝ)/M| ≤
          ε*(((u-l : ℕ) : ℝ)*((t+1 : ℕ) : ℝ)/M) := by
  obtain ⟨T,hT,hbound⟩ := exists_mass_error_threshold ε hε
  refine ⟨T,hT,?_⟩
  intro M _ Q t l u hQ ht hu hmass a
  exact (phase_interval_mass_error M Q t l u hQ ht hu a).trans (hbound _ hmass)

end Erdos66DiscreteRotationMass
