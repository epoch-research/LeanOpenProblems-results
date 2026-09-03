import Submission.LocalPrimeQuantization
import Submission.PrimeLogBoundaryRarity
import Submission.FiniteEndpointTransfer

/-! Fixed locally normalized prime labels are stable in natural mean under
small perturbations, in particular under every fixed positive multiplier. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

/-- Stability of the fixed quantizer under an arbitrary perturbation tending
to zero. The arithmetic input is the absence of mass at its positive levels. -/
theorem localPrimeLabel_perturbation_mean_zero (Q : ℕ) (y : ℕ → ℝ)
    (hy : ∀ n, 0 ≤ y n ∧ y n ≤ 1)
    (he : Tendsto (fun n => y n-localPrimeRatio n) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => prefixMean N
      (fun n => if unitQuantize Q (y n) ≠ localPrimeLabel Q n then (1 : ℝ) else 0)) atTop (𝓝 0) := by
  classical
  rcases Q.eq_zero_or_pos with rfl | hQ
  · simpa [localPrimeLabel,unitQuantize,prefixMean] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let J := Icc 1 Q
  let η := ε/(4*(Q+1 : ℝ))
  have hη : 0 < η := by dsimp [η]; positivity
  have hex (j : J) : ∃ δ > 0, ∀ᶠ N : ℕ in atTop,
      (((range N).filter (fun n => 1<n ∧ |normalizedPrimeLog n n-(j : ℕ)/(Q : ℝ)| ≤ δ)).card : ℝ)/N ≤ η := by
    apply prime_log_level_nonatomic _ _ η hη
    have hj := (mem_Icc.mp j.property).1
    exact div_pos (by exact_mod_cast hj) (by exact_mod_cast hQ)
  choose δ hδ hband using hex
  have heabs := he.abs
  simp only [abs_zero] at heabs
  have hsmall : ∀ᶠ n : ℕ in atTop, ∀ j : J, |localPrimeRatio n-y n| ≤ δ j := by
    apply eventually_all.mpr
    intro j
    filter_upwards [heabs.eventually_lt_const (hδ j)] with n hn
    rw [abs_sub_comm]
    exact hn.le
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp hsmall
  let T := max 2 T₀
  have hbandAll : ∀ᶠ N : ℕ in atTop, ∀ j : J,
      (((range N).filter (fun n => 1<n ∧ |normalizedPrimeLog n n-(j : ℕ)/(Q : ℝ)| ≤ δ j)).card : ℝ)/N ≤ η :=
    eventually_all.mpr hband
  have htail := tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)
  filter_upwards [hbandAll,htail.eventually_lt_const (by positivity : (0 : ℝ)<ε/2)] with N hb ht
  let bad (n : ℕ) : ℝ := if unitQuantize Q (y n) ≠ localPrimeLabel Q n then 1 else 0
  let band (j : J) (n : ℕ) : ℝ := if 1<n ∧ |normalizedPrimeLog n n-(j : ℕ)/(Q : ℝ)| ≤ δ j then 1 else 0
  have hcover (n : ℕ) : bad n ≤ (if n<T then (1 : ℝ) else 0)+∑ j : J, band j n := by
    have hbn (j : J) : 0 ≤ band j n := by dsimp [band]; split_ifs <;> norm_num
    by_cases hnT : n < T
    · rw [if_pos hnT]
      have hbad : bad n ≤ 1 := by dsimp [bad]; split_ifs <;> norm_num
      exact hbad.trans (le_add_of_nonneg_right (sum_nonneg (fun j _ => hbn j)))
    · rw [if_neg hnT,zero_add]
      by_cases hn : unitQuantize Q (y n) = localPrimeLabel Q n
      · simp only [bad,hn,ne_eq,not_true_eq_false,if_false]
        exact sum_nonneg (fun j _ => hbn j)
      · have hn2 : 1 < n := by dsimp [T] at hnT; omega
        have hn₀ : T₀ ≤ n := by dsimp [T] at hnT; omega
        obtain ⟨j,hj,hcross⟩ := unitQuantize_boundary_of_ne Q hQ (localPrimeRatio n) (y n)
          (localPrimeRatio_mem_unit n) (hy n) (Ne.symm hn)
        let j' : J := ⟨j,hj⟩
        have hbj : band j' n = 1 := by
          apply if_pos
          exact ⟨hn2,hcross.trans (hT₀ n hn₀ j')⟩
        have hs := single_le_sum (fun j _ => hbn j) (mem_univ j')
        simpa only [bad,if_pos hn,hbj] using hs
  have hc := sum_le_sum (s := range N) (fun n _ => hcover n)
  rw [sum_add_distrib,sum_comm (s := range N) (t := (univ : Finset J))] at hc
  have hearly : (∑ n ∈ range N, if n<T then (1 : ℝ) else 0) ≤ T := by
    simp only [sum_boole]
    have hh := card_le_card (show (range N).filter (fun n => n<T) ⊆ range T from
      fun n hn => mem_range.mpr (mem_filter.mp hn).2)
    rw [card_range] at hh
    exact_mod_cast hh
  have hb' (j : J) : (∑ n ∈ range N,band j n)/(N : ℝ) ≤ η := by
    simpa only [band,sum_boole] using hb j
  have hsum := sum_le_sum (s := (univ : Finset J)) (fun j _ => hb' j)
  rw [sum_const,card_univ,Fintype.card_coe,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul] at hsum
  have htotal := div_le_div_of_nonneg_right hc (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div] at htotal
  rw [← sum_div] at hsum
  have hear := div_le_div_of_nonneg_right hearly (Nat.cast_nonneg (α := ℝ) N)
  have hQη : (Q : ℝ)*η ≤ ε/4 := by
    dsimp [η]
    have hden : (0 : ℝ)<4*(Q+1) := by positivity
    apply (le_div_iff₀ (by norm_num : (0 : ℝ)<4)).mpr
    field_simp
    nlinarith
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by unfold prefixMean; positivity)]
  change (∑ n ∈ range N,bad n)/(N : ℝ) < ε
  linarith

/-- Fixed positive multipliers alter the fixed local labels only on a set
of natural density zero. This is an averaged statement, not exact equality. -/
theorem localPrimeLabel_mul_mean_zero (Q k : ℕ) (hk : 0 < k) :
    Tendsto (fun N : ℕ => prefixMean N
      (fun n => if localPrimeLabel Q (k*n) ≠ localPrimeLabel Q n then (1 : ℝ) else 0))
      atTop (𝓝 0) :=
  localPrimeLabel_perturbation_mean_zero Q (fun n => localPrimeRatio (k*n))
    (fun n => localPrimeRatio_mem_unit (k*n)) (localPrimeRatio_mul_tendsto k hk)

#print axioms localPrimeLabel_perturbation_mean_zero
#print axioms localPrimeLabel_mul_mean_zero
end Erdos371
