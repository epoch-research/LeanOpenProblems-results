import Submission.HigherChirpPhase

/-! Higher logarithmic phases at their integer root scale. Their multipliers
lie eventually below every larger fixed positive power of the chirp parameter. -/
namespace Erdos371.HigherChirp
open Finset Filter
open scoped Topology
set_option autoImplicit false

def chirpDifferenceBase (r N : ℕ) : ℕ := Nat.nthRoot (r+1) (r.factorial*N)

lemma chirpDifferenceBase_tendsto (r : ℕ) : Tendsto (chirpDifferenceBase r) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b^(r+1))] with N hN
  apply (Nat.le_nthRoot_iff (by omega)).mpr
  exact hN.trans (by simpa only [one_mul] using Nat.mul_le_mul_right N (show 1≤r.factorial from Nat.factorial_pos r))

lemma chirpDifferenceBase_power_bounds (r N : ℕ) :
    chirpDifferenceBase r N ^ (r+1) ≤ r.factorial*N ∧
      r.factorial*N < (chirpDifferenceBase r N+1)^(r+1) :=
  ⟨Nat.pow_nthRoot_le (Or.inl (by omega)),Nat.lt_pow_nthRoot_add_one (by omega) _⟩

/-- The alternating higher logarithmic phase tends to one, for all integer
parameters tending to infinity, not only along perfect powers. -/
theorem higher_chirp_phase_tendsto_one (r : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ)*positiveLogDifference r (chirpDifferenceBase r N)) atTop (𝓝 1) := by
  let m := chirpDifferenceBase r
  have hm : Tendsto (fun N => (m N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (chirpDifferenceBase_tendsto r)
  have hi := tendsto_const_nhds.div_atTop (hm.atTop_add (tendsto_const_nhds (x := (r : ℝ)+1)))
    (a := (r : ℝ)+1)
  have hlo : Tendsto (fun N => ((m N : ℝ)/((m N : ℝ)+r+1))^(r+1)) atTop (𝓝 1) := by
    have h := (hi.const_sub 1).pow (r+1)
    simp only [sub_zero,one_pow] at h
    apply h.congr
    intro N
    dsimp only
    congr 1
    have hden : (m N : ℝ)+r+1≠0 := by positivity
    field_simp
    ring
  have hup : Tendsto (fun N => (((m N : ℝ)+1)/(m N : ℝ))^(r+1)) atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hm).const_add 1
    have hh := h.pow (r+1)
    simp only [add_zero,one_pow] at hh
    apply hh.congr'
    filter_upwards [(chirpDifferenceBase_tendsto r).eventually_gt_atTop 0] with N hN
    dsimp only [m] at *
    congr 1
    have hn : (chirpDifferenceBase r N : ℝ)≠0 := by exact_mod_cast hN.ne'
    field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [(chirpDifferenceBase_tendsto r).eventually_gt_atTop 0] with N hN
    have hnr : (0 : ℝ) < (m N : ℝ) := by exact_mod_cast hN
    have hpow : (m N : ℝ)^(r+1) ≤ (r.factorial : ℝ)*N := by
      exact_mod_cast (chirpDifferenceBase_power_bounds r N).1
    have hd := (positiveLogDifference_bounds r (m N) hnr).1
    have he := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (α := ℝ) N)
    calc
      _ = (m N : ℝ)^(r+1)/((m N : ℝ)+r+1)^(r+1) := div_pow _ _ _
      _ ≤ ((r.factorial : ℝ)*N)/((m N : ℝ)+r+1)^(r+1) := div_le_div_of_nonneg_right hpow (by positivity)
      _ = (N : ℝ)*((r.factorial : ℝ)/((m N : ℝ)+r+1)^(r+1)) := by ring
      _ ≤ _ := he
  · filter_upwards [(chirpDifferenceBase_tendsto r).eventually_gt_atTop 0] with N hN
    have hnr : (0 : ℝ) < (m N : ℝ) := by exact_mod_cast hN
    have hpow : (r.factorial : ℝ)*N≤((m N : ℝ)+1)^(r+1) := by
      exact_mod_cast (chirpDifferenceBase_power_bounds r N).2.le
    have hd := (positiveLogDifference_bounds r (m N) hnr).2
    calc
      _ ≤ (N : ℝ)*((r.factorial : ℝ)/(m N : ℝ)^(r+1)) := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg N)
      _ = ((r.factorial : ℝ)*N)/(m N : ℝ)^(r+1) := by ring
      _ ≤ ((m N : ℝ)+1)^(r+1)/(m N : ℝ)^(r+1) := div_le_div_of_nonneg_right hpow (by positivity)
      _ = _ := (div_pow _ _ _).symm

lemma nthRoot_cast_le_rpow (r N : ℕ) (hr : 0<r) :
    (Nat.nthRoot r N : ℝ) ≤ (N : ℝ)^(1/(r : ℝ)) := by
  have hrr : (0 : ℝ)<r := by exact_mod_cast hr
  have hpow : (Nat.nthRoot r N : ℝ)^r≤(N : ℝ) := by
    exact_mod_cast (Nat.pow_nthRoot_le (n := r) (a := N) (Or.inl hr.ne'))
  have h := Real.rpow_le_rpow (by positivity) hpow (by positivity : (0 : ℝ)≤1/r)
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg _),mul_one_div_cancel hrr.ne',Real.rpow_one] at h
  exact h

lemma chirpDifferenceBase_rpow_bound (r N : ℕ) :
    (chirpDifferenceBase r N : ℝ) ≤
      (r.factorial : ℝ)^(1/(r+1 : ℝ))*(N : ℝ)^(1/(r+1 : ℝ)) := by
  have h := nthRoot_cast_le_rpow (r+1) (r.factorial*N) (by omega)
  simpa only [chirpDifferenceBase,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] using h

/-- The root-scale window is smaller than N^delta whenever 1/(r+1)<delta. -/
theorem chirpDifferenceBase_polynomial_range (r : ℕ) (δ : ℝ) (hδ : 1/(r+1 : ℝ)<δ) :
    ∀ᶠ N : ℕ in atTop, (chirpDifferenceBase r N+r+1 : ℕ) ≤ (N : ℝ)^δ := by
  have hδpos : 0<δ := lt_trans (by positivity) hδ
  have hg := (tendsto_rpow_neg_atTop (sub_pos.mpr hδ)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hm : Tendsto (fun N => (chirpDifferenceBase r N : ℝ)/(N : ℝ)^δ) atTop (𝓝 0) := by
    have hh := hg.const_mul ((r.factorial : ℝ)^(1/(r+1 : ℝ)))
    simp only [mul_zero] at hh
    apply squeeze_zero_norm' _ hh
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNr : (0 : ℝ)<N := by exact_mod_cast hN
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    calc
      _ ≤ ((r.factorial : ℝ)^(1/(r+1 : ℝ))*(N : ℝ)^(1/(r+1 : ℝ)))/(N : ℝ)^δ :=
        div_le_div_of_nonneg_right (chirpDifferenceBase_rpow_bound r N) (by positivity)
      _ = (r.factorial : ℝ)^(1/(r+1 : ℝ))*(N : ℝ)^(-(δ-1/(r+1 : ℝ))) := by
        rw [neg_sub,Real.rpow_sub hNr]
        ring
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδpos).comp tendsto_natCast_atTop_atTop
  have hc := (tendsto_const_nhds (x := (r+1 : ℝ))).div_atTop ht
  have hs := hm.add hc
  simp only [add_zero] at hs
  filter_upwards [hs.eventually_lt_const (by norm_num : (0 : ℝ)<1),eventually_gt_atTop (0 : ℕ)] with N hN hNpos
  have hden : 0<(N : ℝ)^δ := Real.rpow_pos_of_pos (by exact_mod_cast hNpos) _
  have he := (div_lt_one hden).mp (by simpa only [← add_div] using hN)
  push_cast
  linarith

#print axioms higher_chirp_phase_tendsto_one
#print axioms chirpDifferenceBase_polynomial_range
end Erdos371.HigherChirp
