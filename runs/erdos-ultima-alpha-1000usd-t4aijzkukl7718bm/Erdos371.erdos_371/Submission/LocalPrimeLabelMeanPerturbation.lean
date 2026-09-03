import Submission.LocalPrimeLabelStability

/-! Robustness of fixed prime-log labels under endpoint-dependent
perturbations tending to zero in mean, rather than pointwise. -/
namespace Erdos371
open Finset Filter FiniteInformation
open scoped Topology
set_option autoImplicit false

theorem localPrimeLabel_mean_perturbation_zero (Q : ℕ) (y : ℕ → ℕ → ℝ)
    (hy : ∀ N n, n<N → 0 ≤ y N n ∧ y N n ≤ 1)
    (he : Tendsto (fun N => prefixMean N (fun n => |y N n-localPrimeRatio n|)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => prefixMean N
      (fun n => if unitQuantize Q (y N n) ≠ localPrimeLabel Q n then (1 : ℝ) else 0)) atTop (𝓝 0) := by
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
  let C : ℝ := ∑ j : J, 1/δ j
  have hbandAll : ∀ᶠ N : ℕ in atTop, ∀ j : J,
      (((range N).filter (fun n => 1<n ∧ |normalizedPrimeLog n n-(j : ℕ)/(Q : ℝ)| ≤ δ j)).card : ℝ)/N ≤ η :=
    eventually_all.mpr hband
  have ht : Tendsto (fun N : ℕ => (2 : ℝ)/N+C*prefixMean N (fun n => |y N n-localPrimeRatio n|))
      atTop (𝓝 0) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).add (he.const_mul C) using 1
    simp
  filter_upwards [hbandAll,ht.eventually_lt_const (by positivity : (0 : ℝ)<ε/2)] with N hb ht
  let bad (n : ℕ) : ℝ := if unitQuantize Q (y N n) ≠ localPrimeLabel Q n then 1 else 0
  let band (j : J) (n : ℕ) : ℝ := if 1<n ∧ |normalizedPrimeLog n n-(j : ℕ)/(Q : ℝ)| ≤ δ j then 1 else 0
  let E (n : ℕ) := |y N n-localPrimeRatio n|
  have hcover (n : ℕ) (hnN : n<N) :
      bad n ≤ (if n<2 then (1 : ℝ) else 0)+∑ j : J, band j n+E n*C := by
    have hbn (j : J) : 0 ≤ band j n := by dsimp [band]; split_ifs <;> norm_num
    have hE : 0 ≤ E n := abs_nonneg _
    have hC : 0 ≤ C := sum_nonneg (fun j _ => by exact (one_div_pos.mpr (hδ j)).le)
    by_cases hn2 : n<2
    · rw [if_pos hn2]
      have hbad : bad n ≤ 1 := by dsimp [bad]; split_ifs <;> norm_num
      have hs : 0 ≤ ∑ j : J,band j n := sum_nonneg (fun j _ => hbn j)
      have hp : 0 ≤ E n*C := mul_nonneg hE hC
      linarith
    · rw [if_neg hn2,zero_add]
      by_cases hn : unitQuantize Q (y N n) = localPrimeLabel Q n
      · have hbad : bad n=0 := by simp only [bad,hn,ne_eq,not_true_eq_false,if_false]
        rw [hbad]
        exact add_nonneg (sum_nonneg (fun j _ => hbn j)) (mul_nonneg hE hC)
      · obtain ⟨j,hj,hcross⟩ := unitQuantize_boundary_of_ne Q hQ (localPrimeRatio n) (y N n)
          (localPrimeRatio_mem_unit n) (hy N n hnN) (Ne.symm hn)
        let j' : J := ⟨j,hj⟩
        have hpoint : 1 ≤ band j' n+E n/δ j' := by
          by_cases hnear : |normalizedPrimeLog n n-(j : ℝ)/Q| ≤ δ j'
          · have hb' : band j' n=1 := if_pos ⟨by omega,hnear⟩
            rw [hb']
            exact le_add_of_nonneg_right (div_nonneg hE (hδ j').le)
          · have herr : δ j' ≤ E n := by
              rw [abs_sub_comm (localPrimeRatio n) (y N n)] at hcross
              exact (not_le.mp hnear).le.trans hcross
            have hd : 1 ≤ E n/δ j' := (one_le_div (hδ j')).mpr herr
            linarith [hbn j']
        have hsum := single_le_sum (s := (univ : Finset J))
          (fun j _ => add_nonneg (hbn j) (div_nonneg hE (hδ j).le)) (mem_univ j')
        have heq : (∑ j : J, (band j n+E n/δ j)) = (∑ j : J,band j n)+E n*C := by
          rw [sum_add_distrib]
          congr 1
          dsimp [C]
          rw [mul_sum]
          apply sum_congr rfl
          intro j _
          ring
        rw [heq] at hsum
        simpa only [bad,if_pos hn] using hpoint.trans hsum
  have hc := sum_le_sum (s := range N) (fun n hn => hcover n (mem_range.mp hn))
  rw [sum_add_distrib,sum_add_distrib,sum_comm (s := range N) (t := (univ : Finset J)),← sum_mul] at hc
  have hearly : (∑ n ∈ range N, if n<2 then (1 : ℝ) else 0) ≤ 2 := by
    simp only [sum_boole]
    have hh := card_le_card (show (range N).filter (fun n => n<2) ⊆ range 2 from
      fun n hn => mem_range.mpr (mem_filter.mp hn).2)
    rw [card_range] at hh
    exact_mod_cast hh
  have hb' (j : J) : (∑ n ∈ range N,band j n)/(N : ℝ) ≤ η := by
    simpa only [band,sum_boole] using hb j
  have hsum := sum_le_sum (s := (univ : Finset J)) (fun j _ => hb' j)
  rw [sum_const,card_univ,Fintype.card_coe,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,← sum_div] at hsum
  have htotal := div_le_div_of_nonneg_right hc (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div,add_div] at htotal
  have hear := div_le_div_of_nonneg_right hearly (Nat.cast_nonneg (α := ℝ) N)
  have hQη : (Q : ℝ)*η ≤ ε/4 := by
    dsimp [η]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ)<4)).mpr
    field_simp
    nlinarith
  have heq : (∑ n ∈ range N,E n)*C/N = C*prefixMean N (fun n => |y N n-localPrimeRatio n|) := by
    dsimp [E,prefixMean]
    ring
  rw [heq] at htotal
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by unfold prefixMean; positivity)]
  change (∑ n ∈ range N,bad n)/(N : ℝ) < ε
  linarith

#print axioms localPrimeLabel_mean_perturbation_zero
end Erdos371
