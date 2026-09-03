import Submission.RoughCofactors
import Submission.SubpowerSmooth

/-! Grouping comparisons by their larger prime factor. A linear second-moment
bound would suffice for Erdős 371; no such bound is asserted here. -/

namespace Erdos371

open Finset Filter
open scoped Topology

def primeWinner (n : ℕ) : ℕ := max (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n + 1))

def primeWinnerLabels (N : ℕ) : Finset ℕ := insert 1 ((N + 1).primesBelow)

noncomputable def primeWinnerSum (p N : ℕ) : ℝ :=
  ∑ n ∈ (range N).filter (fun n => primeWinner n = p), factorSign n

noncomputable def primeWinnerEnergy (N : ℕ) : ℝ :=
  ∑ p ∈ primeWinnerLabels N, (primeWinnerSum p N) ^ 2

lemma primeWinner_prime_or_one (n : ℕ) : (primeWinner n).Prime ∨ primeWinner n = 1 := by
  rcases n with _ | n
  · simp [primeWinner]
  have hp := Nat.prime_maxPrimeFac_of_one_lt (n + 2) (by omega)
  by_cases h : Nat.maxPrimeFac (n + 1) ≤ Nat.maxPrimeFac (n + 2)
  · simpa only [primeWinner, Nat.add_assoc, Nat.reduceAdd, max_eq_right h] using Or.inl hp
  · have hn : 1 < n + 1 := by
      have hh := Nat.maxPrimeFac_le (n := n + 1)
      have hp2 := hp.two_le
      omega
    exact Or.inl (by
      simpa only [primeWinner, Nat.add_assoc, Nat.reduceAdd, max_eq_left (le_of_not_ge h)] using
        Nat.prime_maxPrimeFac_of_one_lt (n + 1) hn)

lemma primeWinner_mem_labels (N n : ℕ) (hn : n ∈ range N) :
    primeWinner n ∈ primeWinnerLabels N := by
  obtain hp | hp := primeWinner_prime_or_one n
  · apply mem_insert_of_mem
    apply Nat.mem_primesBelow.mpr
    refine ⟨?_, hp⟩
    have hn' := mem_range.mp hn
    have hbound : primeWinner n ≤ n + 1 :=
      max_le (Nat.maxPrimeFac_le.trans (by omega)) Nat.maxPrimeFac_le
    omega
  · simp [primeWinnerLabels, hp]

lemma primeWinnerSum_total (N : ℕ) :
    (∑ p ∈ primeWinnerLabels N, primeWinnerSum p N) =
      (risingCount N : ℝ) - fallingCount N := by
  rw [show (∑ p ∈ primeWinnerLabels N, primeWinnerSum p N) =
      ∑ n ∈ range N, factorSign n from
    sum_fiberwise_of_maps_to (primeWinner_mem_labels N) factorSign]
  unfold factorSign
  rw [predicateSign_sum]
  have hc : (risingCount N : ℝ) + fallingCount N = N := by
    exact_mod_cast comparison_count_partition N
  change 2 * (risingCount N : ℝ) - N = _
  linarith

/-- Cauchy--Schwarz for the prime groups. -/
lemma comparison_sq_le_primeWinnerEnergy (N : ℕ) :
    ((risingCount N : ℝ) - fallingCount N) ^ 2 ≤
      (primeWinnerLabels N).card * primeWinnerEnergy N := by
  have h := sum_mul_sq_le_sq_mul_sq (primeWinnerLabels N) (fun _ => (1 : ℝ))
    (fun p => primeWinnerSum p N)
  simpa only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one,
    primeWinnerSum_total, primeWinnerEnergy] using h

lemma primesBelow_card_rough_bound (B N : ℕ) :
    ((N + 1).primesBelow).card ≤ B + 1 + roughNumberCount B (N + 1) := by
  have hs : (N + 1).primesBelow ⊆ range (B + 1) ∪
      ((range (N + 1)).filter fun p => 1 < p ∧ B < p.minFac) := by
    intro p hp
    obtain ⟨hpN, hp⟩ := Nat.mem_primesBelow.mp hp
    by_cases hb : p ≤ B
    · exact mem_union_left _ (mem_range.mpr (by omega))
    · apply mem_union_right
      exact mem_filter.mpr ⟨mem_range.mpr (by omega), hp.one_lt, by simpa [hp.minFac_eq] using lt_of_not_ge hb⟩
  exact (card_le_card hs).trans (by simpa [roughNumberCount] using (card_union_le
    (range (B + 1)) ((range (N + 1)).filter fun p => 1 < p ∧ B < p.minFac)))

lemma primeWinnerLabels_card_tendsto_zero :
    Tendsto (fun N : ℕ => ((primeWinnerLabels N).card : ℝ) / N) atTop (nhds 0) := by
  have hs : Tendsto Nat.sqrt atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b * b, fun N hN => Nat.le_sqrt.mpr hN⟩
  have ht := (nat_sqrt_add_one_div_tendsto_zero.add
    (growing_roughNumberCount_succ_tendsto Nat.sqrt hs)).add
      tendsto_one_div_atTop_nhds_zero_nat
  simp only [add_zero] at ht
  apply squeeze_zero (fun _ => by positivity) _ ht
  intro N
  rw [← add_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have hc := (card_insert_le 1 ((N + 1).primesBelow)).trans
    (Nat.add_le_add_right (primesBelow_card_rough_bound N.sqrt N) 1)
  exact_mod_cast hc

/-- A sufficient quadratic-energy estimate. Its hypothesis is not proved
in this file and is stronger than the conjecture's signed first-moment bound. -/
theorem density_of_linear_primeWinnerEnergy (C : ℝ)
    (hE : ∀ᶠ N : ℕ in atTop, primeWinnerEnergy N ≤ C * N) :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) := by
  rw [density_iff_signed_count]
  have ht := (primeWinnerLabels_card_tendsto_zero.const_mul C).sqrt
  simp only [mul_zero, Real.sqrt_zero] at ht
  apply squeeze_zero_norm' _ ht
  filter_upwards [hE, eventually_gt_atTop (0 : ℕ)] with N hEN hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := (comparison_sq_le_primeWinnerEnergy N).trans
    (mul_le_mul_of_nonneg_left hEN (Nat.cast_nonneg _))
  apply Real.le_sqrt_of_sq_le
  rw [norm_div, Real.norm_natCast, div_pow, Real.norm_eq_abs, sq_abs]
  apply (div_le_iff₀ (pow_pos hN' 2)).mpr
  convert hs using 1; field_simp

def primeWinnerRises (p N : ℕ) : ℕ :=
  ((range N).filter fun n => primeWinner n = p ∧ Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1)).card

def primeWinnerFalls (p N : ℕ) : ℕ :=
  ((range N).filter fun n => primeWinner n = p ∧ Nat.maxPrimeFac (n + 1) < Nat.maxPrimeFac n).card

/-- An individual prime group's imbalance need not be at most two. -/
lemma primeWinner_23_116_counts : primeWinnerRises 23 116 = 5 ∧ primeWinnerFalls 23 116 = 2 := by
  decide +kernel

lemma not_primeWinner_imbalance_le_two :
    ¬ ∀ p N : ℕ, (primeWinnerRises p N : ℤ) - primeWinnerFalls p N ≤ 2 := by
  intro h
  have hh := h 23 116
  rw [primeWinner_23_116_counts.1, primeWinner_23_116_counts.2] at hh
  norm_num at hh

#print axioms comparison_sq_le_primeWinnerEnergy
#print axioms primeWinnerLabels_card_tendsto_zero
#print axioms density_of_linear_primeWinnerEnergy
#print axioms not_primeWinner_imbalance_le_two

end Erdos371
