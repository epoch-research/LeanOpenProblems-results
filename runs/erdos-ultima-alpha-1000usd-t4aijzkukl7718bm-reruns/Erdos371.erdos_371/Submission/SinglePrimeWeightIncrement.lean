import FormalConjecturesUtil
import Submission.FiniteSupportAdditiveDescent

/-! Raising just the weight at 2, while preserving positive nondecreasing
prime weights, can add linearly many descents. This refutes a proposed
sublinear per-prime induction bound, not Erdős 371 or the uniform half-bound. -/

namespace Erdos371SinglePrimeWeightIncrement

open Finset Filter Erdos371FiniteSupportAdditiveDescent
open Erdos371MonotoneAdditiveReversal (admissible descentMean)
open scoped Topology
attribute [local instance] Classical.propDecidable

noncomputable def base (n : ℕ) : ℝ := Real.log n
noncomputable def increment : ℝ := Real.log 3-Real.log 2
noncomputable def raised (n : ℕ) : ℝ := Real.log n+increment*n.factorization 2

lemma increment_pos : 0 < increment := by
  unfold increment
  exact sub_pos.mpr (Real.log_lt_log (by norm_num) (by norm_num))

lemma raised_eq_height : raised=height {2} 1 (fun _ => increment) := by
  funext n
  simp [raised,height,additive]

lemma base_admissible (N : ℕ) : admissible N base := by
  refine ⟨by simp [base],?_,?_,?_⟩
  · intro a b ha hb
    simp [base,Nat.cast_mul,Real.log_mul (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb)]
  · intro p hp _
    exact Real.log_pos (Nat.one_lt_cast.mpr hp.one_lt)
  · intro p q hp hq hpq _
    exact Real.log_le_log (Nat.cast_pos.mpr hp.pos) (Nat.cast_le.mpr hpq)

lemma raised_prime {p : ℕ} (hp : p.Prime) :
    raised p=if p=2 then Real.log 3 else Real.log p := by
  by_cases hp2 : p=2
  · subst p
    simp [raised,increment,Nat.prime_two.factorization_self]
  · have hn : ¬2 ∣ p := by
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd).symm
    simp [raised,hp2,Nat.factorization_eq_zero_of_not_dvd hn]

lemma raised_admissible (N : ℕ) : admissible N raised := by
  refine ⟨by simp [raised],?_,?_,?_⟩
  · intro a b ha hb
    rw [raised_eq_height]
    exact height_completely_additive _ _ _ ha hb
  · intro p hp _
    rw [raised_prime hp]
    split_ifs
    · exact Real.log_pos (by norm_num)
    · exact Real.log_pos (Nat.one_lt_cast.mpr hp.one_lt)
  · intro p q hp hq hpq _
    rw [raised_prime hp,raised_prime hq]
    by_cases hq2 : q=2
    · have hp2 : p=2 := by have := hp.two_le; omega
      simp [hq2,hp2]
    · by_cases hp2 : p=2
      · simp only [hp2,if_true,if_neg hq2]
        exact Real.log_le_log (by norm_num) (by exact_mod_cast (show 3 ≤ q by have := hq.two_le; omega))
      · simp only [if_neg hp2,if_neg hq2]
        exact Real.log_le_log (Nat.cast_pos.mpr hp.pos) (Nat.cast_le.mpr hpq)

lemma base_no_descent (n : ℕ) : ¬base (n+1)<base n := by
  by_cases hn : n=0
  · simp [hn,base]
  · exact not_lt_of_ge (Real.log_le_log (Nat.cast_pos.mpr (by omega))
      (Nat.cast_le.mpr (Nat.le_succ n)))

lemma raised_even_descent {n : ℕ} (hn : 2<n) (heven : 2 ∣ n) :
    raised (n+1)<raised n := by
  have hn0 : n ≠ 0 := by omega
  have hodd : ¬2 ∣ n+1 := by
    intro h
    exact (by norm_num : ¬2 ∣ 1) ((Nat.dvd_add_iff_right heven).mpr h)
  have hv : (1 : ℝ) ≤ n.factorization 2 :=
    Nat.one_le_cast.mpr (Nat.prime_two.factorization_pos_of_dvd hn0 heven)
  have hlog : Real.log (n+1 : ℕ)<Real.log (n : ℝ)+increment := by
    have hnR : (2 : ℝ)<n := Nat.cast_lt.mpr hn
    have hh : ((n+1 : ℕ) : ℝ)<(n : ℝ)*(3/2) := by push_cast; linarith
    have hl := Real.log_lt_log (by positivity : (0 : ℝ)<(n+1 : ℕ)) hh
    rw [Real.log_mul (Nat.cast_ne_zero.mpr hn0) (by norm_num),
      Real.log_div (by norm_num) (by norm_num)] at hl
    exact hl
  have hm := mul_le_mul_of_nonneg_left hv increment_pos.le
  simp only [raised,Nat.factorization_eq_zero_of_not_dvd hodd,Nat.cast_zero,mul_zero,add_zero]
  linarith

lemma raised_nondivisor_no_descent {n : ℕ} (hn : ¬2 ∣ n) :
    ¬raised (n+1)<raised n := by
  have hn0 : n ≠ 0 := by intro he; subst n; exact hn (dvd_zero 2)
  have hl := Real.log_le_log (Nat.cast_pos.mpr (show 0<n by omega))
    (Nat.cast_le.mpr (Nat.le_succ n))
  have hm := mul_nonneg increment_pos.le (Nat.cast_nonneg (α := ℝ) ((n+1).factorization 2))
  simp only [raised,Nat.factorization_eq_zero_of_not_dvd hn,Nat.cast_zero,mul_zero,add_zero]
  linarith

lemma raised_descent_iff (n : ℕ) : raised (n+1)<raised n ↔ 2<n ∧ 2 ∣ n := by
  constructor
  · intro h
    have hd : 2 ∣ n := by by_contra hh; exact raised_nondivisor_no_descent hh h
    refine ⟨?_,hd⟩
    by_contra hn
    interval_cases n
    · norm_num [raised] at h
    · norm_num at hd
    · have h₂ := raised_prime Nat.prime_two
      have h₃ := raised_prime Nat.prime_three
      norm_num only [if_true,show (2 : ℕ)=2 by rfl,show ¬(3 : ℕ)=2 by decide,if_false] at h₂ h₃
      rw [h₂,h₃] at h
      exact (lt_irrefl _ h)
  · rintro ⟨hn,hd⟩
    exact raised_even_descent hn hd

lemma base_descentCount (N : ℕ) : descentCount base N=0 := by
  unfold descentCount
  rw [filter_eq_empty_iff.mpr (fun n _ => base_no_descent n)]
  rfl

lemma even_count_density : {n : ℕ | 2 ∣ n}.HasDensity (1/2) := by
  apply Erdos371Exploration.periodic_half_density (fun n : ℕ => 2 ∣ n) (Q := 2) (by norm_num)
  · intro n
    exact (Nat.dvd_add_iff_left (dvd_refl 2)).symm
  · decide +kernel

lemma raised_count_bounds (N : ℕ) :
    descentCount raised N ≤ ((range N).filter (fun n => 2 ∣ n)).card ∧
    ((range N).filter (fun n => 2 ∣ n)).card ≤ descentCount raised N+3 := by
  constructor
  · exact card_le_card (fun n hn => mem_filter.mpr
      ⟨(mem_filter.mp hn).1,((raised_descent_iff n).mp (mem_filter.mp hn).2).2⟩)
  · have hs : (range N).filter (fun n => 2 ∣ n) ⊆
        (range N).filter (fun n => raised (n+1)<raised n) ∪ range 3 := by
      intro n hn
      obtain ⟨hnN,hd⟩ := mem_filter.mp hn
      by_cases hh : 2<n
      · exact mem_union_left _ (mem_filter.mpr ⟨hnN,(raised_descent_iff n).mpr ⟨hh,hd⟩⟩)
      · exact mem_union_right _ (mem_range.mpr (by omega))
    exact (card_le_card hs).trans (by simpa only [card_range] using card_union_le _ (range 3))

/-- A single prime-weight increase changes the limiting descent proportion
from zero to one half. Both functions have positive nondecreasing prime weights. -/
theorem raised_descent_mean : Tendsto (descentMean raised) atTop (𝓝 (1/2)) := by
  have he := even_count_density
  simp only [Set.HasDensity,Erdos371Exploration.partialDensity_eq_count] at he
  have hlo : Tendsto (fun N : ℕ =>
      (((range N).filter (fun n => 2 ∣ n)).card : ℝ)/N-3/(N : ℝ)) atTop (𝓝 (1/2)) := by
    simpa using he.sub (tendsto_const_div_atTop_nhds_zero_nat 3)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo he
  · intro N
    rw [descentMean_eq]
    have hc := Nat.cast_le (α := ℝ).mpr (raised_count_bounds N).2
    push_cast at hc
    have hh := div_le_div_of_nonneg_right hc (Nat.cast_nonneg (α := ℝ) N)
    rw [add_div] at hh
    linarith
  · intro N
    rw [descentMean_eq]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (raised_count_bounds N).1)
      (Nat.cast_nonneg (α := ℝ) N)

theorem single_prime_increment_mean :
    Tendsto (fun N : ℕ => descentMean raised N-descentMean base N) atTop (𝓝 (1/2)) := by
  have hh := raised_descent_mean
  change Tendsto (fun N : ℕ => descentMean raised N) atTop (𝓝 (1/2)) at hh
  simpa only [descentMean_eq,base_descentCount,Nat.cast_zero,zero_div,sub_zero] using hh

/-- No `o(N)` allowance can bound this single-prime change in descent count. -/
theorem not_sublinear_single_prime_allowance (E : ℕ → ℝ)
    (hE : Tendsto (fun N : ℕ => E N/N) atTop (𝓝 0)) :
    ¬(∀ᶠ N : ℕ in atTop,
      (descentCount raised N : ℝ)-descentCount base N ≤ E N) := by
  intro h
  have hb : ∀ᶠ N : ℕ in atTop,
      descentMean raised N-descentMean base N ≤ E N/N := by
    filter_upwards [h] with N hN
    rw [descentMean_eq,descentMean_eq,← sub_div]
    exact div_le_div_of_nonneg_right hN (Nat.cast_nonneg (α := ℝ) N)
  have hh := le_of_tendsto_of_tendsto single_prime_increment_mean hE hb
  norm_num at hh

end Erdos371SinglePrimeWeightIncrement

#print axioms Erdos371SinglePrimeWeightIncrement.raised_admissible
#print axioms Erdos371SinglePrimeWeightIncrement.raised_descent_iff
#print axioms Erdos371SinglePrimeWeightIncrement.single_prime_increment_mean

#print axioms Erdos371SinglePrimeWeightIncrement.not_sublinear_single_prime_allowance
