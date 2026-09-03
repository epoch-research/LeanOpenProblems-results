import FormalConjecturesUtil

/-! A linear lower bound at arbitrarily large cutoffs forces divergence of
the reciprocal-weighted series of a nonnegative sequence. -/
namespace Erdos972LinearPrefixDivergence

open Finset

lemma not_summable_div_succ_of_frequently_linear {a : ℕ → ℝ} {c : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hc : 0 < c)
    (hlinear : ∀ B : ℕ, ∃ N : ℕ, B < N ∧ c * N < ∑ n ∈ Ioc 0 N, a n) :
    ¬ Summable (fun n : ℕ => a n / ((n+1 : ℕ) : ℝ)) := by
  intro hs
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hs (c/4) (by positivity)
  let C : ℝ := ∑ n ∈ s, a n
  have hC : 0 ≤ C := sum_nonneg fun n _ => ha n
  obtain ⟨B, hB⟩ := exists_nat_gt (2*C/c + 1)
  obtain ⟨N, hBN, hN⟩ := hlinear B
  have hNR : (2*C/c + 1) < (N : ℝ) := hB.trans (Nat.cast_lt.mpr hBN)
  have hN1 : (1 : ℝ) ≤ N := by
    have hdiv : 0 ≤ 2*C/c := by positivity
    linarith
  have hCN : C < c * N / 2 := by
    have hh : 2*C/c < (N : ℝ) := by linarith
    have := (div_lt_iff₀ hc).mp hh
    nlinarith
  let t := Ioc 0 N \ s
  have hdis : Disjoint t s := by
    apply disjoint_left.mpr
    intro n hn hns
    exact (mem_sdiff.mp hn).2 hns
  have ht := hs t hdis
  have hsum0 : 0 ≤ ∑ n ∈ t, a n / ((n+1 : ℕ) : ℝ) :=
    sum_nonneg fun n _ => div_nonneg (ha n) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg hsum0] at ht
  have htail : (∑ n ∈ t, a n) ≤ ((N : ℝ)+1) * (c/4) := by
    calc
      _ ≤ ((N : ℝ)+1) * ∑ n ∈ t, a n / ((n+1 : ℕ) : ℝ) := by
        rw [mul_sum]
        apply sum_le_sum
        intro n hn
        have hnN : n ≤ N := (mem_Ioc.mp (mem_sdiff.mp hn).1).2
        have hden : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
        have hratio : 0 ≤ a n / ((n+1 : ℕ) : ℝ) := div_nonneg (ha n) hden.le
        calc
          a n = (((n+1 : ℕ) : ℝ)) * (a n / ((n+1 : ℕ) : ℝ)) := by
            field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hnN) hratio
      _ ≤ _ := mul_le_mul_of_nonneg_left ht.le (by positivity)
  have hfront : (∑ n ∈ Ioc 0 N ∩ s, a n) ≤ C :=
    sum_le_sum_of_subset_of_nonneg inter_subset_right (fun n _ _ => ha n)
  have he := sum_inter_add_sum_diff (Ioc 0 N) s a
  change _ + ∑ n ∈ t, a n = _ at he
  nlinarith

#print axioms not_summable_div_succ_of_frequently_linear

end Erdos972LinearPrefixDivergence
