import Submission.LargePrimeDensityLower
import Submission.PrimeReflection

/-! A positive proportion of indices below an endpoint are reflected beyond
that endpoint. Thus this reflection does not pair almost all indices within
the same counting interval. This does not disprove comparison balance. -/

namespace Erdos371
open Finset Filter
open FiniteSieve

lemma filter_count_le_shifted_add_one (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    ((range N).filter P).card ≤ ((range N).filter (fun n => P (n+1))).card + 1 := by
  have h := sum_range_succ' (fun n => if P n then (1 : ℕ) else 0) N
  rw [sum_range_succ] at h
  simp only [sum_boole,Nat.cast_id] at h
  have h' : ((range N).filter P).card + (if P N then 1 else 0) =
      ((range N).filter (fun n => P (n+1))).card + (if P 0 then 1 else 0) := by
    convert h using 2
  split_ifs at h' <;> omega

lemma primeReflection_ge_of_product_ge (N n : ℕ) (hn : n < N)
    (hp : 2*N ≤ pairPrimeProduct n) : N ≤ primeReflection n := by
  have hs : n < pairPrimeProduct n := by omega
  rw [primeReflection_mod_free n hs]
  omega

lemma reflection_boundary_cover_eventually :
    ∀ᶠ N : ℕ in atTop, ∀ n < N,
      (N : ℝ)^(1999/2000 : ℝ) < Nat.maxPrimeFac (n+1) →
        N ≤ primeReflection n ∨ (Nat.maxPrimeFac n : ℝ) ≤ (N : ℝ)^(1/1000 : ℝ) := by
  have ht := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2000)).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop (2 : ℝ)
  filter_upwards [ht,eventually_gt_atTop (0 : ℕ)] with N hN hNpos
  intro n hn hq
  by_cases hp : (Nat.maxPrimeFac n : ℝ) ≤ (N : ℝ)^(1/1000 : ℝ)
  · exact Or.inr hp
  · apply Or.inl
    apply primeReflection_ge_of_product_ge N n hn
    have hn0 : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hpr : (2 : ℝ)*N ≤ (Nat.maxPrimeFac n : ℝ)*Nat.maxPrimeFac (n+1) := by
      calc
        _ ≤ (N : ℝ)*(N : ℝ)^(1/2000 : ℝ) := by
          dsimp only [Function.comp_def] at hN
          nlinarith
        _ = (N : ℝ)^(1/1000 : ℝ)*(N : ℝ)^(1999/2000 : ℝ) := by
          rw [← Real.rpow_add hn0]
          calc
            _ = (N : ℝ)^(1+(1/2000 : ℝ)) := by rw [Real.rpow_add hn0,Real.rpow_one]
            _ = _ := by congr 1; norm_num
        _ ≤ _ := mul_le_mul (le_of_lt (lt_of_not_ge hp)) hq.le
          (Real.rpow_nonneg hn0.le _) (Nat.cast_nonneg _)
    exact_mod_cast hpr

/-- A quantitative obstruction to reflection within a natural counting
interval: at least `1/10000` of its inputs eventually leave the interval. -/
theorem primeReflection_boundary_positive_proportion :
    ∀ᶠ N : ℕ in atTop, (1/10000 : ℝ) ≤
      (((range N).filter (fun n => N ≤ primeReflection n)).card : ℝ)/N := by
  classical
  have hhigh := largePrime_power_count_eventually_ge (1999/2000 : ℝ) (by norm_num)
    (by norm_num) (1/100000 : ℝ) (by norm_num)
  have hlow := smooth_power_count_eventually_le (1/1000 : ℝ) (by norm_num)
    (1/100000 : ℝ) (by norm_num)
  have hone := tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const
    (by norm_num : (0 : ℝ) < 1/100000)
  filter_upwards [hhigh,hlow,hone,reflection_boundary_cover_eventually] with N hh hl ho hcover
  let H := (range N).filter (fun n => (N : ℝ)^(1999/2000 : ℝ) < (Nat.maxPrimeFac (n+1) : ℝ))
  let L := (range N).filter (fun n => (Nat.maxPrimeFac n : ℝ) ≤ (N : ℝ)^(1/1000 : ℝ))
  let E := (range N).filter (fun n => N ≤ primeReflection n)
  have hsub : H ⊆ E ∪ L := by
    intro n hn
    obtain ⟨hnN,hq⟩ := mem_filter.mp hn
    rcases hcover n (mem_range.mp hnN) hq with he | hl
    · exact mem_union_left _ (mem_filter.mpr ⟨hnN,he⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hnN,hl⟩)
  have hc := (card_le_card hsub).trans (card_union_le E L)
  have hs := filter_count_le_shifted_add_one
    (fun n => (Nat.maxPrimeFac n : ℝ) ≤ (N : ℝ)^(1/1000 : ℝ)) N
  have hbound : H.card ≤ E.card +
      ((range N).filter (fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^(1/1000 : ℝ))).card + 1 := by
    change L.card ≤ _ at hs
    omega
  have hr := div_le_div_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr hbound) (Nat.cast_nonneg (α := ℝ) N)
  simp only [Nat.cast_add,Nat.cast_one,add_div] at hr
  dsimp only [H,E] at hr
  norm_num at hh hl
  linarith

/-- The number of reflected indices crossing the endpoint is not `o(N)`. -/
theorem primeReflection_boundary_not_negligible :
    ¬Tendsto (fun N : ℕ =>
      (((range N).filter (fun n => N ≤ primeReflection n)).card : ℝ)/N) atTop (nhds 0) := by
  classical
  intro ht
  have hsmall := ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1/10000)
  obtain ⟨N,hN,hN'⟩ := (primeReflection_boundary_positive_proportion.and hsmall).exists
  linarith

#print axioms primeReflection_boundary_positive_proportion
#print axioms primeReflection_boundary_not_negligible
end Erdos371
