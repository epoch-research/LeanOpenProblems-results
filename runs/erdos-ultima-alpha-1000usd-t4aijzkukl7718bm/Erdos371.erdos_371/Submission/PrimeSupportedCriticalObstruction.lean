import Submission.WeightedPrimeHarmonic

/-!
An auxiliary prime-supported array separating unweighted square convergence
from critical prime-weighted convergence. Its support lies in the interior
power band (X^(1/3), X^(2/3)] when X=N^3. This is NOT the array of arithmetic
comparison currents, and is NOT a disproof of Erdős 371.
-/
namespace Erdos371.PrimeSupportedCriticalObstruction
open Finset Filter FiniteSieve
open scoped Topology
set_option autoImplicit false

noncomputable def band (N : ℕ) : Finset ℕ :=
  ((N^2+1).primesBelow).filter (N < ·)

lemma mem_band (N p : ℕ) :
    p ∈ band N ↔ p.Prime ∧ N < p ∧ p ≤ N^2 := by
  simp only [band,mem_filter,Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨hpN,hp⟩,hNp⟩
    exact ⟨hp,hNp,by omega⟩
  · rintro ⟨hp,hNp,hpN⟩
    exact ⟨⟨by omega,hp⟩,hNp⟩

noncomputable def mass (N : ℕ) : ℝ := ∑ p ∈ band N, (1 : ℝ)/p

noncomputable def logMass (N : ℕ) : ℝ :=
  ∑ p ∈ band N, Real.log p/(p : ℝ)

lemma mass_nonneg (N : ℕ) : 0 ≤ mass N := by
  unfold mass
  positivity

lemma logMass_eq_sub (N : ℕ) (hN : 1 ≤ N) :
    logMass N = primeLogHarmonic (N^2)-primeLogHarmonic N := by
  have hsplit := sum_filter_add_sum_filter_not ((N^2+1).primesBelow)
    (fun p => N < p) (fun p => Real.log p/(p : ℝ))
  have hsmall : ((N^2+1).primesBelow).filter (fun p => ¬ N < p) =
      (N+1).primesBelow := by
    ext p
    simp only [mem_filter,Nat.mem_primesBelow]
    have hNN : N ≤ N^2 := by nlinarith
    constructor
    · rintro ⟨⟨_,hp⟩,hNp⟩
      exact ⟨by omega,hp⟩
    · rintro ⟨hpN,hp⟩
      exact ⟨⟨by omega,hp⟩,by omega⟩
  rw [hsmall] at hsplit
  change logMass N+primeLogHarmonic N=primeLogHarmonic (N^2) at hsplit
  linarith

lemma logMass_bounds (N : ℕ) (hN : 2 ≤ N) :
    Real.log N*mass N ≤ logMass N ∧
      logMass N ≤ (2*Real.log N)*mass N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  constructor
  · unfold mass logMass
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨hpp,hNp,_⟩ := (mem_band N p).mp hp
    have hl := Real.log_le_log hN0 (show (N : ℝ) ≤ p by exact_mod_cast hNp.le)
    simpa only [mul_one_div] using div_le_div_of_nonneg_right hl (Nat.cast_nonneg p)
  · unfold mass logMass
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨hpp,_,hpN⟩ := (mem_band N p).mp hp
    have hl := Real.log_le_log (show (0 : ℝ) < p by exact_mod_cast hpp.pos)
      (show (p : ℝ) ≤ (N : ℝ)^2 by exact_mod_cast hpN)
    rw [Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    simpa only [mul_one_div] using div_le_div_of_nonneg_right hl (Nat.cast_nonneg p)

lemma logMass_nonneg (N : ℕ) : 0 ≤ logMass N := by
  unfold logMass
  exact sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

lemma mass_eventually_bounds :
    ∀ᶠ N : ℕ in atTop, (1/4 : ℝ) ≤ mass N ∧ mass N ≤ 3 := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    hlog.eventually_ge_atTop (2*(1+primePowerErrorConstant+Real.log 4)),
    hlog.eventually_ge_atTop (Real.log 4)] with N hN hlarge hfour
  have hN0 : 0 < N := by omega
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hlow := primeLogHarmonic_lower (N^2) (pow_pos hN0 2)
  have hupp := primeLogHarmonic_upper N hN0
  have htop := primeLogHarmonic_upper (N^2) (pow_pos hN0 2)
  have hsmall : 0 ≤ primeLogHarmonic N := by
    unfold primeLogHarmonic
    exact sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have he : Real.log ((N^2 : ℕ) : ℝ)=2*Real.log N := by
    push_cast
    rw [Real.log_pow]
    norm_num
  rw [he] at hlow htop
  have hbounds := logMass_bounds N hN
  have hsub := logMass_eq_sub N (by omega)
  constructor <;> nlinarith

/-- An artificial current, supported only on primes in a fixed interior band. -/
noncomputable def current (N p : ℕ) : ℝ :=
  if p ∈ band N then 1/(p : ℝ) else 0

lemma current_nonneg (N p : ℕ) : 0 ≤ current N p := by
  unfold current
  split_ifs <;> positivity

lemma current_eq_zero_of_le (N p : ℕ) (hp : p ≤ N) : current N p=0 := by
  have hnot : p ∉ band N := by rw [mem_band]; omega
  simp only [current,hnot,if_false]

lemma current_fixed_label_zero (p : ℕ) :
    Tendsto (fun N => current N p) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop p] with N hN
  exact (current_eq_zero_of_le N p hN).symm

lemma current_support (N p : ℕ) (h : current N p ≠ 0) :
    p.Prime ∧ N < p ∧ p ≤ N^2 := by
  by_contra hn
  have hnot : p ∉ band N := (mem_band N p).not.mpr hn
  exact h (by simp only [current,hnot,if_false])

lemma current_reciprocal_bound (N p : ℕ) : |current N p| ≤ 1/(p : ℝ) := by
  rw [abs_of_nonneg (current_nonneg N p)]
  unfold current
  split_ifs
  · exact le_rfl
  · positivity

lemma current_weighted_square (N p : ℕ) :
    (p : ℝ)*(current N p)^2=current N p := by
  unfold current
  split_ifs with hp
  · have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast ((mem_band N p).mp hp).1.ne_zero
    field_simp
  · ring

lemma current_l1_eq (N : ℕ) :
    (∑ p ∈ band N, |current N p|)=mass N := by
  unfold mass
  apply sum_congr rfl
  intro p hp
  simp only [current,hp,if_true,abs_of_nonneg (show (0 : ℝ) ≤ 1/p by positivity)]

lemma current_critical_energy_eq (N : ℕ) :
    (∑ p ∈ band N, (p : ℝ)*(current N p)^2)=mass N := by
  simp only [current_weighted_square]
  unfold mass
  apply sum_congr rfl
  intro p hp
  simp only [current,hp,if_true]

lemma current_square_sum_bound (N : ℕ) (hN : 0 < N) :
    (∑ p ∈ band N, (current N p)^2) ≤ mass N/(N : ℝ) := by
  unfold mass
  rw [sum_div]
  apply sum_le_sum
  intro p hp
  have hNp := ((mem_band N p).mp hp).2.1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hi : 1/(p : ℝ) ≤ 1/(N : ℝ) :=
    one_div_le_one_div_of_le hN0 (by exact_mod_cast hNp.le)
  simp only [current,hp,if_true]
  have hm := mul_le_mul_of_nonneg_left hi (show (0 : ℝ) ≤ 1/p by positivity)
  convert hm using 1 <;> ring

/-- Unweighted square convergence has a power-saving bound, while the
critical prime-weighted energy stays bounded away from zero. -/
theorem current_square_sum_zero :
    Tendsto (fun N => ∑ p ∈ band N, (current N p)^2) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun N => sum_nonneg fun _ _ => sq_nonneg _) _
    (tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ))
  filter_upwards [mass_eventually_bounds,eventually_gt_atTop (0 : ℕ)] with N hb hN
  exact (current_square_sum_bound N hN).trans
    (div_le_div_of_nonneg_right hb.2 (Nat.cast_nonneg N))

theorem current_critical_energy_not_zero :
    ¬ Tendsto (fun N => ∑ p ∈ band N, (p : ℝ)*(current N p)^2) atTop (𝓝 0) := by
  intro h
  simp only [current_critical_energy_eq] at h
  obtain ⟨N,hN,hu⟩ := (mass_eventually_bounds.and
    (h.eventually_lt_const (by norm_num : (0 : ℝ) < 1/4))).exists
  exact hu.not_ge hN.1

theorem current_l1_not_zero :
    ¬ Tendsto (fun N => ∑ p ∈ band N, |current N p|) atTop (𝓝 0) := by
  simpa only [current_l1_eq,current_critical_energy_eq] using current_critical_energy_not_zero

/-- Every additional nonnegative weight tending to zero does give convergence.
Thus even this entire family of subcritical conclusions does not upgrade to
critical convergence without additional information about the currents. -/
theorem current_slack_energy_zero (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p)
    (hw0 : Tendsto w atTop (𝓝 0)) :
    Tendsto (fun N => ∑ p ∈ band N, w p*((p : ℝ)*(current N p)^2))
      atTop (𝓝 0) := by
  simp only [current_weighted_square]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨B,hB⟩ := eventually_atTop.mp (hw0.eventually_lt_const
    (show (0 : ℝ) < ε/4 by positivity))
  filter_upwards [mass_eventually_bounds,eventually_ge_atTop B] with N hb hNB
  have hnon : 0 ≤ ∑ p ∈ band N, w p*current N p :=
    sum_nonneg fun p _ => mul_nonneg (hw p) (current_nonneg N p)
  have hbound : (∑ p ∈ band N, w p*current N p) ≤ (ε/4)*mass N := by
    unfold mass
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hNp := ((mem_band N p).mp hp).2.1
    have hwp := hB p (by omega)
    simp only [current,hp,if_true]
    exact mul_le_mul_of_nonneg_right hwp.le (by positivity)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnon]
  nlinarith

lemma current_square_tsum_eq (N : ℕ) :
    (∑' p : ℕ, (current N p)^2)=∑ p ∈ band N, (current N p)^2 := by
  apply tsum_eq_sum
  intro p hp
  simp only [current,hp,if_false,zero_pow (by omega : (2 : ℕ) ≠ 0)]

lemma current_weighted_tsum_eq (w : ℕ → ℝ) (N : ℕ) :
    (∑' p : ℕ, w p*((p : ℝ)*(current N p)^2))=
      ∑ p ∈ band N, w p*((p : ℝ)*(current N p)^2) := by
  apply tsum_eq_sum
  intro p hp
  simp only [current,hp,if_false,zero_pow (by omega : (2 : ℕ) ≠ 0),mul_zero]

/-- A precise failed analytic upgrade. Even retaining prime support in an
interior band, the reciprocal coordinate bound, unweighted square convergence,
and EVERY vanishing extra weight does not force the critical energy to zero.
This assertion concerns arbitrary arrays, not the actual comparison currents. -/
theorem not_prime_supported_critical_upgrade :
    ¬ (∀ c : ℕ → ℕ → ℝ,
      (∀ N p, c N p ≠ 0 → p.Prime ∧ N < p ∧ p ≤ N^2) →
      (∀ N p, |c N p| ≤ 1/(p : ℝ)) →
      Tendsto (fun N => ∑' p : ℕ, (c N p)^2) atTop (𝓝 0) →
      (∀ w : ℕ → ℝ, (∀ p, 0 ≤ w p) → Tendsto w atTop (𝓝 0) →
        Tendsto (fun N => ∑' p : ℕ, w p*((p : ℝ)*(c N p)^2)) atTop (𝓝 0)) →
      Tendsto (fun N => ∑' p : ℕ, (p : ℝ)*(c N p)^2) atTop (𝓝 0)) := by
  intro h
  have hs : Tendsto (fun N => ∑' p : ℕ, (current N p)^2) atTop (𝓝 0) := by
    simpa only [current_square_tsum_eq] using current_square_sum_zero
  have hw : ∀ w : ℕ → ℝ, (∀ p, 0 ≤ w p) → Tendsto w atTop (𝓝 0) →
      Tendsto (fun N => ∑' p : ℕ, w p*((p : ℝ)*(current N p)^2)) atTop (𝓝 0) := by
    intro w hpos ht
    simpa only [current_weighted_tsum_eq] using current_slack_energy_zero w hpos ht
  have hh := h current current_support current_reciprocal_bound hs hw
  have he (N : ℕ) : (∑' p : ℕ, (p : ℝ)*(current N p)^2)=
      ∑ p ∈ band N, (p : ℝ)*(current N p)^2 := by
    simpa only [one_mul] using current_weighted_tsum_eq (fun _ => 1) N
  simp only [he] at hh
  exact current_critical_energy_not_zero hh

#print axioms not_prime_supported_critical_upgrade
#print axioms mass_eventually_bounds
#print axioms current_square_sum_zero
#print axioms current_critical_energy_not_zero
#print axioms current_slack_energy_zero
end Erdos371.PrimeSupportedCriticalObstruction
