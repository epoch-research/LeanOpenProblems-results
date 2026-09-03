import Submission.BothLargePrimeBound
import Submission.LargePrimeDensityLower

/-! Positive lower proportions for both orientations of the largest-prime-
factor comparison. This is weaker than existence of density or density one half. -/

namespace Erdos371
open Finset Filter
open FiniteSieve

lemma filter_count_shifted_le_add_one (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    ((range N).filter (fun n => P (n+1))).card ≤ ((range N).filter P).card+1 := by
  have h := sum_range_succ' (fun n => if P n then (1 : ℕ) else 0) N
  rw [sum_range_succ] at h
  simp only [sum_boole,Nat.cast_id] at h
  have h' : ((range N).filter P).card + (if P N then 1 else 0) =
      ((range N).filter (fun n => P (n+1))).card + (if P 0 then 1 else 0) := by
    convert h using 2
  split_ifs at h' <;> omega

lemma large_factor_count_le_rises_add_both (N : ℕ) (u : ℝ) :
    ((range N).filter (fun n => (N : ℝ)^(1-u) < (Nat.maxPrimeFac (n+1) : ℝ))).card ≤
      risingCount N + (bothLargePrimeSet N u).card := by
  classical
  have hsub : (range N).filter (fun n => (N : ℝ)^(1-u) < (Nat.maxPrimeFac (n+1) : ℝ)) ⊆
      ((range N).filter (fun n => Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1))) ∪ bothLargePrimeSet N u := by
    intro n hn
    obtain ⟨hnN,hq⟩ := mem_filter.mp hn
    by_cases h : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
    · exact mem_union_left _ (mem_filter.mpr ⟨hnN,h⟩)
    · have h' : (Nat.maxPrimeFac (n+1) : ℝ) ≤ Nat.maxPrimeFac n := by exact_mod_cast (not_lt.mp h)
      exact mem_union_right _ (mem_filter.mpr ⟨hnN,hq.trans_le h',hq⟩)
  exact (card_le_card hsub).trans (card_union_le _ _)

lemma large_factor_count_le_falls_add_both (N : ℕ) (u : ℝ) :
    ((range N).filter (fun n => (N : ℝ)^(1-u) < (Nat.maxPrimeFac (n+1) : ℝ))).card ≤
      fallingCount N + (bothLargePrimeSet N u).card+1 := by
  classical
  have hshift := filter_count_shifted_le_add_one
    (fun n => (N : ℝ)^(1-u) < (Nat.maxPrimeFac n : ℝ)) N
  have hsub : (range N).filter (fun n => (N : ℝ)^(1-u) < (Nat.maxPrimeFac n : ℝ)) ⊆
      ((range N).filter (fun n => Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n)) ∪ bothLargePrimeSet N u := by
    intro n hn
    obtain ⟨hnN,hp⟩ := mem_filter.mp hn
    by_cases h : Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n
    · exact mem_union_left _ (mem_filter.mpr ⟨hnN,h⟩)
    · have h' : (Nat.maxPrimeFac n : ℝ) ≤ Nat.maxPrimeFac (n+1) := by exact_mod_cast (not_lt.mp h)
      exact mem_union_right _ (mem_filter.mpr ⟨hnN,hp,hp.trans_le h'⟩)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  exact hshift.trans (Nat.add_le_add_right hc 1)

/-- Both strict comparison directions occur with a positive lower natural
proportion. This theorem makes no assertion that their densities exist. -/
theorem rising_falling_positive_lower_proportions :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop,
      δ ≤ (risingCount N : ℝ)/N ∧ δ ≤ (fallingCount N : ℝ)/N := by
  classical
  have hK : 0 ≤ largePairConstant := by unfold largePairConstant; positivity
  let u : ℝ := 1/(8*(largePairConstant+1))
  have hden : 0 < 8*(largePairConstant+1) := by positivity
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu : u ≤ 1/8 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hKu : largePairConstant*u ≤ 1/8 := by
    dsimp only [u]
    rw [mul_one_div]
    apply (div_le_iff₀ hden).mpr
    linarith
  have hKu2 : largePairConstant*u^2 ≤ u/8 := by
    have h := mul_le_mul_of_nonneg_right hKu hu0.le
    nlinarith
  have heps : 0 < u/8 := by positivity
  have hhigh := largePrime_power_count_eventually_ge (1-u) (by linarith) (by linarith) (u/8) heps
  have hboth := bothLargePrimeSet_eventually_ratio_le u hu0.le hu (u/8) heps
  have hone := tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const heps
  refine ⟨u/4,by positivity,?_⟩
  filter_upwards [hhigh,hboth,hone] with N hh hb ho
  have hcr := div_le_div_of_nonneg_right
    ((Nat.cast_le (α := ℝ)).mpr (large_factor_count_le_rises_add_both N u)) (Nat.cast_nonneg (α := ℝ) N)
  have hcf := div_le_div_of_nonneg_right
    ((Nat.cast_le (α := ℝ)).mpr (large_factor_count_le_falls_add_both N u)) (Nat.cast_nonneg (α := ℝ) N)
  simp only [Nat.cast_add,Nat.cast_one,add_div] at hcr hcf
  constructor <;> linarith

/-- In particular, density zero is ruled out for the rising comparison. -/
theorem rising_comparison_not_density_zero :
    ¬({n | Nat.maxPrimeFac (n+1) > Nat.maxPrimeFac n}.HasDensity 0) := by
  intro hd
  obtain ⟨δ,hδ,hboth⟩ := rising_falling_positive_lower_proportions
  have ht := (density_iff_count _ 0).mp hd
  have hs := ht.eventually_lt_const hδ
  obtain ⟨N,hN,hN'⟩ := (hboth.and hs).exists
  change (risingCount N : ℝ)/N < δ at hN'
  linarith [hN.1]

/-- Density zero is also ruled out for the falling comparison. -/
theorem falling_comparison_not_density_zero :
    ¬({n | Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n}.HasDensity 0) := by
  intro hd
  obtain ⟨δ,hδ,hboth⟩ := rising_falling_positive_lower_proportions
  have ht := (density_iff_count _ 0).mp hd
  have hs := ht.eventually_lt_const hδ
  obtain ⟨N,hN,hN'⟩ := (hboth.and hs).exists
  change (fallingCount N : ℝ)/N < δ at hN'
  linarith [hN.2]

#print axioms rising_falling_positive_lower_proportions
#print axioms rising_comparison_not_density_zero
#print axioms falling_comparison_not_density_zero
end Erdos371
