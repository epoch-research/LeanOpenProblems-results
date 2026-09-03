import FormalConjecturesUtil
import Submission.UniformPowerSkew
import Submission.PrimeDeletionVariance

/-! The mean absolute normalized prime-power increment is zero in the limit
at exponent zero, but one at every fixed positive exponent. This is a
nonuniformity result, not a disproof of Erdős 371 or a signed cancellation theorem. -/

namespace Erdos371NormalizedPowerBoundary

open Finset Filter Erdos371UniformPowerSkew Erdos371SmallPrimeAveraging
open Erdos371PrimeDeletionVariance Erdos371ReflectionRange
open Erdos371NormalizedAdditiveDiscrepancy (skew skew_abs_le)
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def omega (n : ℕ) : ℝ := n.primeFactors.card

lemma omega_nonneg (n : ℕ) : 0≤omega n := Nat.cast_nonneg _

lemma omega_zero : omega 0=0 := by simp [omega]

lemma powerSum_zero (n : ℕ) : powerSum 0 n=omega n := by
  simp [powerSum,omega]

lemma omega_succ_eq_smallCount {n N : ℕ} (hn : n<N) :
    omega (n+1)=smallCount (N+1).primesBelow n := by
  rw [omega,smallCount_eq_card]
  apply congrArg (fun fs : Finset ℕ => (fs.card:ℝ))
  ext p
  simp only [Nat.mem_primeFactors,mem_filter,Nat.mem_primesBelow]
  constructor
  · rintro ⟨hp,hd,_⟩
    refine ⟨⟨?_,hp⟩,hd⟩
    have hh := Nat.le_of_dvd (show 0<n+1 by omega) hd
    omega
  · rintro ⟨⟨_,hp⟩,hd⟩
    exact ⟨hp,hd,by omega⟩

lemma mean_abs_le_sqrt_mean_sq (f : ℕ → ℝ) (N : ℕ) :
    mean (fun n => |f n|) N ≤ Real.sqrt (mean (fun n => (f n)^2) N) := by
  by_cases hN : N=0
  · subst N
    simp [mean]
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  apply Real.le_sqrt_of_sq_le
  have hh := sum_mul_sq_le_sq_mul_sq (range N) (fun _ => (1:ℝ)) (fun n => |f n|)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,card_range,sq_abs] at hh
  unfold mean
  rw [div_pow]
  calc
    _ ≤ ((N:ℝ)*(∑ n ∈ range N, (f n)^2))/(N:ℝ)^2 :=
      div_le_div_of_nonneg_right hh (sq_nonneg _)
    _ = _ := by field_simp

lemma successor_prime_card_le (N : ℕ) : (N+1).primesBelow.card≤N := by
  have hs : (N+1).primesBelow ⊆ Ico 1 (N+1) := by
    intro p hp
    obtain ⟨hpN,hp⟩ := Nat.mem_primesBelow.mp hp
    exact mem_Ico.mpr ⟨hp.one_lt.le,hpN⟩
  simpa only [Nat.card_Ico,Nat.add_sub_cancel] using card_le_card hs

lemma deviation_shift_bound (N : ℕ) :
    mean (fun n => |omega (n+1)-primeMass (N+1)|) N ≤
      Real.sqrt (3*primeMass (N+1)) := by
  have he : mean (fun n => (omega (n+1)-primeMass (N+1))^2) N =
      varianceMean (N+1).primesBelow N := by
    unfold varianceMean mean
    congr 1
    apply sum_congr rfl
    intro n hn
    dsimp only
    rw [omega_succ_eq_smallCount (mem_range.mp hn)]
    rfl
  calc
    _ ≤ Real.sqrt (mean (fun n => (omega (n+1)-primeMass (N+1))^2) N) :=
      mean_abs_le_sqrt_mean_sq _ N
    _ = Real.sqrt (varianceMean (N+1).primesBelow N) := by rw [he]
    _ ≤ _ := Real.sqrt_le_sqrt (varianceMean_le_three_mass _
      (fun _ hp => Nat.prime_of_mem_primesBelow hp) N (successor_prime_card_le N))

lemma mean_shift_upper {f : ℕ → ℝ} (hf : ∀ n, 0≤f n) (N : ℕ) :
    mean f N ≤ mean (fun n => f (n+1)) N + f 0/N := by
  have hh := sum_range_succ' f N
  rw [sum_range_succ] at hh
  have hb : (∑ n ∈ range N, f n) ≤ (∑ n ∈ range N, f (n+1))+f 0 := by
    linarith [hf N]
  simpa only [mean,add_div] using div_le_div_of_nonneg_right hb (Nat.cast_nonneg (α := ℝ) N)

lemma deviation_bound (N : ℕ) :
    mean (fun n => |omega n-primeMass (N+1)|) N ≤
      Real.sqrt (3*primeMass (N+1))+primeMass (N+1)/N := by
  have hh := mean_shift_upper (f := fun n => |omega n-primeMass (N+1)|)
    (fun _ => abs_nonneg _) N
  rw [omega_zero,zero_sub,abs_neg,abs_of_nonneg (show 0≤primeMass (N+1) from mass_nonneg _)] at hh
  exact hh.trans (add_le_add (deviation_shift_bound N) le_rfl)

lemma skew_abs_le_deviation {a b M : ℝ} (ha : 0≤a) (hb : 0≤b) (hM : 0<M) :
    |skew a b| ≤ (|a-M|+|b-M|)/M := by
  by_cases h : M≤a+b
  · have hab : 0<a+b := hM.trans_le h
    have ht : |b-a|≤|a-M|+|b-M| := by
      calc
        _ = |(b-M)-(a-M)| := by congr 1; ring
        _ ≤ |b-M|+|a-M| := abs_sub _ _
        _ = _ := add_comm _ _
    rw [skew,abs_div,abs_of_pos hab]
    exact (div_le_div_of_nonneg_right ht hab.le).trans
      (div_le_div_of_nonneg_left (by positivity) hM h)
  · apply (skew_abs_le ha hb).trans
    apply (le_div_iff₀ hM).mpr
    have h₁ := neg_le_abs (a-M)
    have h₂ := neg_le_abs (b-M)
    linarith

lemma mean_div_const (f : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    mean (fun n => f n/c) N = mean f N/c := by
  simp [mean,sum_div,div_div,mul_comm]

lemma zero_exponent_absolute_mean_bound {N : ℕ} (hM : 0<primeMass (N+1)) :
    mean (fun n => |normalized 0 n|) N ≤
      2*((Real.sqrt (3*primeMass (N+1))+2)/primeMass (N+1))+1/N := by
  let M := primeMass (N+1)
  have hp (n : ℕ) : |normalized 0 n| ≤
      (|omega n-M|+|omega (n+1)-M|)/M := by
    simp only [normalized,powerSum_zero]
    exact skew_abs_le_deviation (omega_nonneg n) (omega_nonneg (n+1)) hM
  have hh := mean_mono hp N
  rw [mean_div_const,mean_add] at hh
  have hD := deviation_bound N
  have hD' := deviation_shift_bound N
  change mean (fun n => |omega n-M|) N ≤ Real.sqrt (3*M)+M/N at hD
  change mean (fun n => |omega (n+1)-M|) N ≤ Real.sqrt (3*M) at hD'
  calc
    _ ≤ (mean (fun n => |omega n-M|) N + mean (fun n => |omega (n+1)-M|) N)/M := hh
    _ ≤ (2*Real.sqrt (3*M)+M/N)/M :=
      div_le_div_of_nonneg_right (by linarith) hM.le
    _ = 2*Real.sqrt (3*M)/M+1/N := by dsimp [M]; field_simp
    _ ≤ _ := by
      change 2*Real.sqrt (3*M)/M+1/N ≤ 2*((Real.sqrt (3*M)+2)/M)+1/N
      have hpos : 0≤(4:ℝ)/M := by positivity
      have he : 2*((Real.sqrt (3*M)+2)/M) = 2*Real.sqrt (3*M)/M+4/M := by ring
      rw [he]
      linarith

/-- At exponent zero the power sum is the distinct-prime-divisor count.
Its concentration makes even the absolute normalized adjacent increment small. -/
theorem zero_exponent_absolute_mean_tendsto_zero :
    Tendsto (mean (fun n => |normalized 0 n|)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun N : ℕ => N+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro K
    filter_upwards [eventually_ge_atTop K] with N hN
    omega
  have hu := ((root_error_tendsto_zero.comp hshift).const_mul 2).add
    tendsto_one_div_atTop_nhds_zero_nat
  simp only [mul_zero,add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall (fun N => mean_nonneg (fun _ => abs_nonneg _) N)
  · filter_upwards [(primeMass_tendsto_atTop.comp hshift).eventually
      (eventually_gt_atTop 0)] with N hM
    exact zero_exponent_absolute_mean_bound hM

/-- The absolute-value limits jump at zero. This rules out uniform
mean-absolute interpolation across zero, not the original density conjecture. -/
theorem absolute_mean_boundary :
    Tendsto (mean (fun n => |normalized 0 n|)) atTop (𝓝 0) ∧
    ∀ s : ℝ, 0<s → Tendsto (mean (fun n => |normalized s n|)) atTop (𝓝 1) := by
  refine ⟨zero_exponent_absolute_mean_tendsto_zero, fun s hs => ?_⟩
  exact absolute_mean_tendsto_one (fun _ => s) hs (Eventually.of_forall (fun _ => le_rfl))

lemma zero_exponent_signed_mean_tendsto_zero :
    Tendsto (mean (normalized 0)) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    zero_exponent_absolute_mean_tendsto_zero
  · intro N
    exact abs_nonneg _
  · intro N
    change |mean (normalized 0) N| ≤ mean (fun n => |normalized 0 n|) N
    unfold mean
    rw [abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)

/-- Even arbitrarily far out in the counting range there is no uniform
continuity in the exponent at zero for the mean absolute increment. -/
theorem arbitrarily_late_boundary_separation {η : ℝ} (hη : 0<η) (N₀ : ℕ) :
    ∃ N : ℕ, N₀≤N ∧ ∃ s : ℝ, 0<s ∧ s<η ∧
      1/2 < |mean (fun n => |normalized s n|) N -
        mean (fun n => |normalized 0 n|) N| := by
  have hp := absolute_mean_tendsto_one (fun _ => η/2) (half_pos hη)
    (Eventually.of_forall (fun _ => le_rfl))
  have ht := hp.sub zero_exponent_absolute_mean_tendsto_zero
  simp only [sub_zero] at ht
  have hg := ht.eventually (lt_mem_nhds (show (1/2:ℝ)<1 by norm_num))
  obtain ⟨N,hN,hbound⟩ := ((eventually_ge_atTop N₀).and hg).exists
  refine ⟨N,hN,η/2,half_pos hη,by linarith,?_⟩
  exact hbound.trans_le (le_abs_self _)

end Erdos371NormalizedPowerBoundary

#print axioms Erdos371NormalizedPowerBoundary.zero_exponent_absolute_mean_tendsto_zero
#print axioms Erdos371NormalizedPowerBoundary.absolute_mean_boundary

#print axioms Erdos371NormalizedPowerBoundary.zero_exponent_signed_mean_tendsto_zero
#print axioms Erdos371NormalizedPowerBoundary.arbitrarily_late_boundary_separation
