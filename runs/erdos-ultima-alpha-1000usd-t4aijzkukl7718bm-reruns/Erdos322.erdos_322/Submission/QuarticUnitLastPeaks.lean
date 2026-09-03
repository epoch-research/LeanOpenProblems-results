import Submission.QuarticUnitLastCount
import Submission.APPrimeProducts

/-! Divisor-scale lower bounds for primitive quartic representations with
one coordinate exactly one. The threshold is subpolynomial, not a fixed power. -/
namespace Erdos322Research.QuarticUnitLastPeaks
noncomputable section
open Finset Filter QuarticUnitLastCount APPrimeProducts
open scoped Classical Topology
set_option Elab.async false
set_option maxHeartbeats 0

/-- A common-target primitive family with explicit height control. -/
theorem divisor_scale_family (R : ℕ) :
    ∃ r n : ℕ, R ≤ r ∧ 3 ≤ r ∧ 0 < n ∧ 2^r < count n ∧ n ≤ r^(36*r) := by
  obtain ⟨S,hR,hS,hp,hB⟩ := exists_prime_set_small_product (1 : ZMod 3)
    isUnit_one (max (R+3) 6)
  have hsplit : ∀ p ∈ S, p.Prime ∧ 3 ∣ p-1 := by
    intro p hpS
    have hh := hp p hpS
    refine ⟨hh.1,?_⟩
    have he : p ≡ 1 [MOD 3] := (ZMod.natCast_eq_natCast_iff _ _ 3).mp hh.2
    have hsub := Nat.ModEq.sub_right hh.1.one_lt.le (by omega : 1 ≤ 1) he
    exact Nat.modEq_zero_iff_dvd.mp (by simpa using hsub)
  let s := S.card
  let r := s-3
  let M := ∏ p ∈ S,p
  let n := 2*M^2+1
  have hs6 : 6 ≤ s := (le_max_right _ _).trans hR
  have hsR : R+3 ≤ s := (le_max_left _ _).trans hR
  have hr3 : 3 ≤ r := by dsimp [r]; omega
  have hsr : s=r+3 := by dsimp [r]; omega
  have hM : 0 < M := prod_pos fun p hpS ↦ (hsplit p hpS).1.pos
  have hcount := prime_product_count S hsplit
  have hpow : 2^s=8*2^r := by rw [hsr,pow_add]; norm_num; ring
  have hlarge : 2^r < count n := by
    change 2^s ≤ 4*count n at hcount
    rw [hpow] at hcount
    have hpos : 0 < 2^r := pow_pos (by decide) _
    nlinarith
  have hns : n ≤ s^(9*s) := by
    have hM2 : 1 ≤ M^2 := one_le_pow₀ (by omega)
    calc
      n ≤ s*M^2 := by dsimp [n]; nlinarith
      _ ≤ s*(s^(4*s))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB 2)
      _ = s^(8*s+1) := by rw [← pow_mul,← pow_succ']; congr 1; ring
      _ ≤ s^(9*s) := Nat.pow_le_pow_right (by omega) (by omega)
  have hheight : n ≤ r^(36*r) := by
    have hsmall : s ≤ r^2 := by rw [hsr]; nlinarith
    calc
      n ≤ s^(9*s) := hns
      _ ≤ (r^2)^(9*s) := Nat.pow_le_pow_left hsmall _
      _ ≤ r^(36*r) := by
        rw [← pow_mul]
        apply Nat.pow_le_pow_right (by omega)
        rw [hsr]
        omega
  exact ⟨r,n,by dsimp [r]; omega,hr3,by dsimp [n]; omega,hlarge,hheight⟩

private lemma logarithmic_height_bound (r n : ℕ) (hr : 0 < r)
    (hn : 0 < n) (hlog : 1 ≤ Real.log (Real.log (n : ℝ)))
    (hheight : n ≤ r^(36*r)) :
    Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)) ≤ 36*(r : ℝ) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hLpos : 0 < Real.log (Real.log (n : ℝ)) := by linarith
  apply (div_le_iff₀ hLpos).mpr
  by_cases hsmall : Real.log (n : ℝ) ≤ r
  · nlinarith
  · have hrl : Real.log (r : ℝ) ≤ Real.log (Real.log (n : ℝ)) :=
      Real.log_le_log hrp (le_of_not_ge hsmall)
    have hh : Real.log (n : ℝ) ≤ (36*(r : ℝ))*Real.log (r : ℝ) := by
      have hcast : (n : ℝ) ≤ (r : ℝ)^(36*r) := by exact_mod_cast hheight
      have hh := Real.log_le_log hnp hcast
      simpa only [Real.log_pow,Nat.cast_mul,Nat.cast_ofNat] using hh
    exact hh.trans (mul_le_mul_of_nonneg_left hrl (by positivity))

/-- Infinitely many exact primitive counts exceed a fixed divisor-scale
threshold. All counted tuples have fourth coordinate one. -/
theorem exp_log_div_loglog_peaks :
    {n : ℕ | Real.exp ((Real.log 2/36)*
      (Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)))) < count n}.Infinite := by
  have hc : 0 < Real.log 2/36 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  apply Set.infinite_of_forall_exists_gt
  have ht : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 1)
  intro b
  let T := max N (b+1)
  let D := (range T).sup count
  obtain ⟨r,n,hR,hr3,hn,hcount,hheight⟩ := divisor_scale_family (D+1)
  have hr : 0 < r := by omega
  have hnT : T ≤ n := by
    by_contra hh
    have hnmem : n ∈ range T := mem_range.mpr (by omega)
    have hbd : count n ≤ D := le_sup hnmem
    have htwr : r < 2^r := Nat.lt_two_pow_self
    omega
  have hlog : 1 ≤ Real.log (Real.log (n : ℝ)) := hN n ((le_max_left _ _).trans hnT)
  have hbound := logarithmic_height_bound r n hr hn hlog hheight
  have hexp : Real.exp ((Real.log 2/36)*
      (Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)))) ≤ (2 : ℝ)^r := by
    calc
      _ ≤ Real.exp ((Real.log 2/36)*(36*(r : ℝ))) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbound hc.le)
      _ = Real.exp ((r : ℝ)*Real.log 2) := by congr 1; ring
      _ = (2 : ℝ)^r := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  refine ⟨n,hexp.trans_lt (by exact_mod_cast hcount),?_⟩
  have hbT : b+1 ≤ T := le_max_right _ _
  omega

/-- The same explicit threshold also bounds the unrestricted count from below. -/
theorem full_count_exp_log_div_loglog_peaks :
    {n : ℕ | Real.exp ((Real.log 2/36)*
      (Real.log (n : ℝ)/Real.log (Real.log (n : ℝ)))) <
        Erdos322.representationCount 4 n}.Infinite := by
  apply exp_log_div_loglog_peaks.mono
  intro n hn
  exact lt_of_lt_of_le hn (show (count n : ℝ) ≤ Erdos322.representationCount 4 n from
    by exact_mod_cast count_le_full n)

end
end Erdos322Research.QuarticUnitLastPeaks
