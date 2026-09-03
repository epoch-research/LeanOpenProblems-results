import FormalConjecturesUtil
import Submission.BoundedCofactorCancellation

/-! A logarithmically small energy bound for winning primes with bounded
cofactor at a COMMON counting endpoint. The cofactor bound is fixed; the
unbounded-cofactor part of the total energy remains uncontrolled. -/

namespace Erdos371BoundedCofactorEnergy

open Finset Filter Erdos371PrimeDiscrepancy Erdos371CofactorDiscrepancy
open Erdos371BoundedCofactorCancellation
open scoped Topology

attribute [local instance] Classical.propDecidable

noncomputable def boundary (p N : ℕ) : ℝ :=
  if P N = p ∧ P (N+1) < p then 1 else 0

lemma boundary_nonneg (p N : ℕ) : 0 ≤ boundary p N := by
  unfold boundary
  split_ifs <;> norm_num

lemma group_eq_boundary_of_regular {A p N : ℕ} (hp : p.Prime) (hAp : A < p)
    (hr : regular A p) (hNA : N/p ≤ A) : (group p N : ℝ) = boundary p N := by
  have hsub : Finset.Icc 1 (N/p) ⊆ Finset.Icc 1 A := by
    intro a ha
    obtain ⟨ha1,haN⟩ := Finset.mem_Icc.mp ha
    exact Finset.mem_Icc.mpr ⟨ha1,haN.trans hNA⟩
  have hgood (a : ℕ) (ha : a ∈ Finset.Icc 1 (N/p)) :
      P a ≤ p ∧ P (a*p-1) < p ∧ P (a*p+1) < p := by
    have haA := (Finset.mem_Icc.mp (hsub ha)).2
    exact ⟨Nat.maxPrimeFac_le.trans (by omega),hr a (hsub ha)⟩
  have hm : ((Finset.Icc 1 (N/p)).filter fun a => P a ≤ p ∧ P (a*p-1) < p) =
      Finset.Icc 1 (N/p) := Finset.filter_eq_self.mpr (fun a ha =>
        ⟨(hgood a ha).1,(hgood a ha).2.1⟩)
  have hp' : ((Finset.Icc 1 (N/p)).filter fun a => P a ≤ p ∧ P (a*p+1) < p) =
      Finset.Icc 1 (N/p) := Finset.filter_eq_self.mpr (fun a ha =>
        ⟨(hgood a ha).1,(hgood a ha).2.2⟩)
  have he := group_eq_cofactorDifference hp N
  rw [cofactorDifference,hm,hp',sub_self,zero_add] at he
  unfold boundary
  exact_mod_cast he

noncomputable def highPrimes (A N : ℕ) : Finset ℕ :=
  (N+1).primesBelow.filter fun p => N/p ≤ A

noncomputable def highEnergy (A N : ℕ) : ℝ :=
  ∑ p ∈ highPrimes A N, (group p N : ℝ)^2

lemma highEnergy_nonneg (A N : ℕ) : 0 ≤ highEnergy A N :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma highEnergy_bound (A N : ℕ) :
    highEnergy A N ≤ (A:ℝ)^2*(irregularPrimes A (N+1)).card+1 := by
  have hpoint (p : ℕ) (hp : p ∈ highPrimes A N) :
      (group p N : ℝ)^2 ≤
        (A:ℝ)^2*(if p ∈ irregularPrimes A (N+1) then 1 else 0)+boundary p N := by
    obtain ⟨hpN,hNA⟩ := Finset.mem_filter.mp hp
    have hp' := Nat.prime_of_mem_primesBelow hpN
    by_cases hb : p ∈ irregularPrimes A (N+1)
    · rw [if_pos hb,mul_one]
      have hg := (Erdos371ElementaryEnergy.group_abs_le_div hp' N).trans
        (Nat.cast_le.mpr hNA)
      have hsq := (sq_le_sq₀ (abs_nonneg (group p N : ℝ)) (Nat.cast_nonneg A)).mpr hg
      rw [sq_abs] at hsq
      exact hsq.trans (le_add_of_nonneg_right (boundary_nonneg p N))
    · have hh : ¬(p ≤ A ∨ ¬regular A p) := by
        intro h
        exact hb (Finset.mem_filter.mpr ⟨hpN,h⟩)
      have hAp : A < p := Nat.lt_of_not_ge (not_or.mp hh).1
      have hr : regular A p := not_not.mp (not_or.mp hh).2
      rw [if_neg hb,mul_zero,zero_add,group_eq_boundary_of_regular hp' hAp hr hNA]
      unfold boundary
      split_ifs <;> norm_num
  have hcard : ((highPrimes A N).filter fun p => p ∈ irregularPrimes A (N+1)).card ≤
      (irregularPrimes A (N+1)).card := by
    apply Finset.card_le_card
    exact fun p hp => (Finset.mem_filter.mp hp).2
  have hb : (∑ p ∈ highPrimes A N, boundary p N) ≤ 1 := by
    have he : (∑ p ∈ (N+1).primesBelow, boundary p N) =
        if P (N+1) < P N then (1:ℝ) else 0 := by
      unfold boundary
      exact_mod_cast endpoint_sum N
    calc
      _ ≤ ∑ p ∈ (N+1).primesBelow, boundary p N :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _ _ => boundary_nonneg p N)
      _ ≤ 1 := by rw [he]; split_ifs <;> norm_num
  have hs := Finset.sum_le_sum hpoint
  change highEnergy A N ≤ _ at hs
  rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_boole] at hs
  exact hs.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hcard) (sq_nonneg _)) hb)

lemma log_shift_ratio_bound {N : ℕ} (hN : 0 < N) :
    Real.log (N:ℝ)/N ≤ 2*Real.log (N+1:ℕ)/(N+1:ℕ) := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hn1 : (0:ℝ) < (N+1:ℕ) := by positivity
  apply (div_le_div_iff₀ hn hn1).mpr
  have hlog := Real.log_le_log hn (show (N:ℝ) ≤ (N+1:ℕ) by exact_mod_cast Nat.le_succ N)
  have hsize : ((N+1:ℕ):ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast (by omega : N+1 ≤ 2*N)
  calc
    _ ≤ Real.log (N+1:ℕ)*(N+1:ℕ) := mul_le_mul_of_nonneg_right hlog hn1.le
    _ ≤ Real.log (N+1:ℕ)*(2*N) :=
      mul_le_mul_of_nonneg_left hsize (Real.log_natCast_nonneg (N+1))
    _ = _ := by ring

/-- For each fixed positive `A`, the energy from primes satisfying `N/p≤A`
is `o(N/log N)`. This is not a bound for the full winning-prime energy. -/
theorem highEnergy_log_ratio_tendsto_zero {A : ℕ} (hA : 0 < A) :
    Tendsto (fun N : ℕ => highEnergy A N*Real.log N/N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)/N) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hshift : Tendsto (fun N : ℕ =>
      ((irregularPrimes A (N+1)).card:ℝ)*Real.log (N+1:ℕ)/(N+1:ℕ)) atTop (𝓝 0) := by
    exact (irregularPrimes_log_ratio_tendsto_zero hA).comp (tendsto_add_atTop_nat 1)
  have hu := hlog.add (hshift.const_mul (2*(A:ℝ)^2))
  simp only [mul_zero,add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun N =>
      div_nonneg (mul_nonneg (highEnergy_nonneg A N) (Real.log_natCast_nonneg N)) (Nat.cast_nonneg N)
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hratio := log_shift_ratio_bound hN
    have hm := mul_le_mul_of_nonneg_right (highEnergy_bound A N)
      (div_nonneg (Real.log_natCast_nonneg N) (Nat.cast_nonneg N))
    have hsmall := mul_le_mul_of_nonneg_left hratio
      (show 0 ≤ (A:ℝ)^2*((irregularPrimes A (N+1)).card:ℝ) by positivity)
    calc
      _ = highEnergy A N*(Real.log N/N) := by ring
      _ ≤ ((A:ℝ)^2*((irregularPrimes A (N+1)).card:ℝ)+1)*(Real.log N/N) := hm
      _ = Real.log N/N+(A:ℝ)^2*((irregularPrimes A (N+1)).card:ℝ)*(Real.log N/N) := by ring
      _ ≤ Real.log N/N+(A:ℝ)^2*((irregularPrimes A (N+1)).card:ℝ)*
          (2*Real.log (N+1:ℕ)/(N+1:ℕ)) := add_le_add le_rfl hsmall
      _ = _ := by ring

end Erdos371BoundedCofactorEnergy

#print axioms Erdos371BoundedCofactorEnergy.highEnergy_bound
#print axioms Erdos371BoundedCofactorEnergy.highEnergy_log_ratio_tendsto_zero
