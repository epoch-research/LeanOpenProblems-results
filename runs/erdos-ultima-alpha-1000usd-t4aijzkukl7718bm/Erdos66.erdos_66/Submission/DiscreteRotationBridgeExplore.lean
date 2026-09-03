import Submission.ShortRotationLogBoundExplore
import Submission.ShortOrbitCarryExplore

/-! Exact bridge from integer rotations to the finite cyclic carry indicator. -/
namespace Erdos66DiscreteRotationBridge
open Erdos66ShortOrbitCarry Erdos66RotationFloorPerturbation
  Erdos66ShortRotationLogBound
open scoped Classical
set_option maxHeartbeats 1800000

lemma ediv_difference (v n T : ℤ) (hn : 0 < n) (hT : 0 ≤ T) (hTn : T ≤ n) :
    v/n-(v-T)/n = if v % n < T then 1 else 0 := by
  have hr0 := Int.emod_nonneg v hn.ne'
  have hrn := Int.emod_lt_of_pos v hn
  have he : v-T=(v % n-T)+n*(v/n) := by
    have hh := Int.emod_add_mul_ediv v n
    omega
  rw [he,Int.add_ediv_of_dvd_right (dvd_mul_right n (v/n)),Int.mul_ediv_cancel_left _ hn.ne']
  by_cases h : v % n < T
  · rw [if_pos h,Int.ediv_eq_neg_one_of_neg_of_le (a := v % n-T) (b := n) (by omega) (by omega)]
    omega
  · rw [if_neg h,Int.ediv_eq_zero_of_lt (a := v % n-T) (b := n) (by omega) (by omega)]
    omega

variable (M : ℕ) [NeZero M]

lemma hit_floor (m : ℤ) (a : ZMod M) (t k : ℕ) (ht : t < M) :
    hit M (m : ZMod M) a t k =
      ((⌊(a.val : ℝ)/M+(k : ℝ)*((m : ℝ)/M)⌋ -
        ⌊(a.val : ℝ)/M+(k : ℝ)*((m : ℝ)/M)-((t+1 : ℕ) : ℝ)/M⌋ : ℤ) : ℝ) := by
  let v : ℤ := m*(k : ℤ)+(a.val : ℤ)
  have hval : (((m : ZMod M)*(k : ZMod M)+a).val : ℤ) = v % (M : ℤ) := by
    have he : (v : ZMod M)=(m : ZMod M)*(k : ZMod M)+a := by
      simp [v]
    rw [← he]
    exact ZMod.val_intCast v
  have he1 : (a.val : ℝ)/M+(k : ℝ)*((m : ℝ)/M)=(v : ℝ)/M := by
    simp only [v,Int.cast_add,Int.cast_mul,Int.cast_natCast]
    ring
  have he2 : (v : ℝ)/M-((t+1 : ℕ) : ℝ)/M=((v-(t+1 : ℕ) : ℤ) : ℝ)/M := by
    push_cast
    ring
  rw [he1,he2,Int.floor_div_natCast,Int.floor_div_natCast,Int.floor_intCast,Int.floor_intCast]
  have hM : (0 : ℤ) < M := by exact_mod_cast NeZero.pos M
  rw [ediv_difference v M ((t+1 : ℕ) : ℤ) hM (by positivity) (by exact_mod_cast Nat.succ_le_iff.mpr ht)]
  unfold hit
  have hc : v % (M : ℤ) < (t+1 : ℕ) ↔ ((m : ZMod M)*(k : ZMod M)+a).val ≤ t := by
    rw [← hval]
    omega
  simp only [hc]
  split_ifs <;> norm_num

lemma hit_range_eq_rotationSum (m : ℤ) (a : ZMod M) (t N : ℕ) (ht : t < M) :
    (∑ k ∈ Finset.range N, hit M (m : ZMod M) a t k) =
      rotationSum ((m : ℝ)/M) ((a.val : ℝ)/M) (((t+1 : ℕ) : ℝ)/M) N := by
  unfold rotationSum
  exact Finset.sum_congr rfl (fun k _ ↦ hit_floor M m a t k ht)

omit [NeZero M] in
lemma hit_add (b a : ZMod M) (t l k : ℕ) :
    hit M b a t (l+k) = hit M b (b*(l : ZMod M)+a) t k := by
  unfold hit
  have he : b*((l+k : ℕ) : ZMod M)+a=b*(k : ZMod M)+(b*(l : ZMod M)+a) := by
    push_cast
    ring
  rw [he]

noncomputable def phaseInteger : ℤ := ⌊(M : ℝ)*Real.sqrt 2⌋
noncomputable def phase : ZMod M := (phaseInteger M : ZMod M)

lemma slope_error : |((phaseInteger M : ℤ) : ℝ)/M-Real.sqrt 2| ≤ 1/(M : ℝ) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hlo := Int.floor_le ((M : ℝ)*Real.sqrt 2)
  have hhi := Int.lt_floor_add_one ((M : ℝ)*Real.sqrt 2)
  have hle : ((phaseInteger M : ℤ) : ℝ)/M ≤ Real.sqrt 2 := by
    apply (div_le_iff₀ hM).mpr
    simpa [phaseInteger,mul_comm] using hlo
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  apply (le_div_iff₀ hM).mpr
  have he : -( ((phaseInteger M : ℤ) : ℝ)/M-Real.sqrt 2)*(M : ℝ) =
      (M : ℝ)*Real.sqrt 2-((phaseInteger M : ℤ) : ℝ) := by field_simp; ring
  rw [he]
  change (M : ℝ)*Real.sqrt 2-((⌊(M : ℝ)*Real.sqrt 2⌋ : ℤ) : ℝ) ≤ 1
  linarith

lemma slope_near (Q : ℕ) (hQ : Q^2 ≤ M) :
    (Q : ℝ)^2*|((phaseInteger M : ℤ) : ℝ)/M-Real.sqrt 2| ≤ 1 := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hQR : (Q : ℝ)^2 ≤ M := by exact_mod_cast hQ
  calc
    _ ≤ (Q : ℝ)^2*(1/(M : ℝ)) := mul_le_mul_of_nonneg_left (slope_error M) (sq_nonneg _)
    _ ≤ (M : ℝ)*(1/(M : ℝ)) := mul_le_mul_of_nonneg_right hQR (by positivity)
    _ = 1 := by field_simp

/-- This same explicit phase works for every target and every short horizon. -/
theorem phase_intervalBound (Q t : ℕ) (hQ : Q^2 ≤ M) (ht : t < M) :
    IntervalBound M (phase M) Q t (25*Real.log ((Q : ℝ)+1)) := by
  intro a l u _ hu
  rw [Finset.sum_Ico_eq_sum_range]
  simp_rw [hit_add]
  rw [phase,hit_range_eq_rotationSum M (phaseInteger M) _ t (u-l) ht]
  have hNQ : u-l ≤ Q := (Nat.sub_le u l).trans hu
  have he := rotation_log_bound (((phaseInteger M : ℤ) : ℝ)/M) Q (slope_near M Q hQ)
    (u-l) hNQ ((((phaseInteger M : ZMod M))*(l : ZMod M)+a).val/M : ℝ)
    (((t+1 : ℕ) : ℝ)/M)
  have hlog : Real.log (((u-l : ℕ) : ℝ)+1) ≤ Real.log ((Q : ℝ)+1) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right hNQ 1
  simpa only [mul_div_assoc] using he.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))

end Erdos66DiscreteRotationBridge
