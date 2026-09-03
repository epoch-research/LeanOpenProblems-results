import Submission.PrimeWinnerFlux

/-! An unconditional upper bound for the full prime-winner energy. This
is a sparsity bound, not the near-linear signed energy estimate needed
for the density conjecture. -/

namespace Erdos371
open Finset Filter
open scoped Topology

lemma primeWinnerSum_norm_le_group_card (p N : ℕ) :
    ‖primeWinnerSum p N‖ ≤ (((range N).filter (fun n => primeWinner n = p)).card : ℝ) := by
  unfold primeWinnerSum
  simpa only [factorSign_norm, sum_const, nsmul_eq_mul, mul_one] using
    norm_sum_le ((range N).filter (fun n => primeWinner n = p)) factorSign

lemma primeWinnerSum_norm_sum_le (N : ℕ) :
    (∑ p ∈ primeWinnerLabels N, ‖primeWinnerSum p N‖) ≤ N := by
  calc
    _ ≤ ∑ p ∈ primeWinnerLabels N,
        (((range N).filter (fun n => primeWinner n = p)).card : ℝ) :=
      sum_le_sum fun p _ => primeWinnerSum_norm_le_group_card p N
    _ = _ := by
      have h := sum_fiberwise_of_maps_to (primeWinner_mem_labels N) (fun _ => (1 : ℝ))
      simpa only [sum_const, nsmul_eq_mul, mul_one, card_range] using h

lemma primeWinnerSum_low_norm_sum_le (B N : ℕ) :
    (∑ p ∈ (primeWinnerLabels N).filter (· ≤ B), ‖primeWinnerSum p N‖) ≤
      (((range N).filter (fun n => Nat.maxPrimeFac n ≤ B)).card : ℝ) := by
  let S := (primeWinnerLabels N).filter (· ≤ B)
  calc
    _ ≤ ∑ p ∈ S, (((range N).filter (fun n => primeWinner n = p)).card : ℝ) :=
      sum_le_sum fun p _ => primeWinnerSum_norm_le_group_card p N
    _ = (((range N).filter (fun n => primeWinner n ∈ S)).card : ℝ) := by
      exact_mod_cast sum_card_fiberwise_eq_card_filter (range N) S primeWinner
    _ ≤ _ := by
      exact_mod_cast card_le_card (show (range N).filter (fun n => primeWinner n ∈ S) ⊆
          (range N).filter (fun n => Nat.maxPrimeFac n ≤ B) from by
        intro n hn
        obtain ⟨hnN, hp⟩ := mem_filter.mp hn
        have hB := (mem_filter.mp hp).2
        exact mem_filter.mpr ⟨hnN, (le_max_left _ _).trans hB⟩)

lemma primeWinnerSum_high_norm_bound (B p N : ℕ) (hp : B < p) :
    ‖primeWinnerSum p N‖ ≤ 2 * (N : ℝ) / (B+1) + 1 := by
  have hpp : 0 < p := by omega
  have hd : ((N/p : ℕ) : ℝ) ≤ (N : ℝ)/(B+1) := by
    apply (Nat.cast_div_le (m := N) (n := p) (α := ℝ)).trans
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity)
      (by exact_mod_cast (show B+1 ≤ p by omega))
  have h := primeWinnerSum_norm_le_multiples p N
  calc
    _ ≤ 2 * ((N/p : ℕ) : ℝ) + 1 := h
    _ ≤ 2 * ((N : ℝ)/(B+1)) + 1 := by gcongr
    _ = _ := by ring

/-- Splitting at any prime cutoff gives a fully unconditional finite bound.
No cancellation inside a prime group is used in this inequality. -/
theorem primeWinnerEnergy_bulk_upper (B N : ℕ) :
    primeWinnerEnergy N ≤
      ((((range N).filter (fun n => Nat.maxPrimeFac n ≤ B)).card : ℝ))^2 +
        (2 * (N : ℝ) / (B+1) + 1) * N := by
  let L := (primeWinnerLabels N).filter (· ≤ B)
  let H := (primeWinnerLabels N).filter (B < ·)
  have he : primeWinnerEnergy N =
      (∑ p ∈ L, (primeWinnerSum p N)^2) + (∑ p ∈ H, (primeWinnerSum p N)^2) := by
    unfold primeWinnerEnergy
    dsimp [L, H]
    rw [sum_filter, sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    by_cases h : p ≤ B <;> simp [h, lt_iff_not_ge]
  have hL : (∑ p ∈ L, (primeWinnerSum p N)^2) ≤
      ((((range N).filter (fun n => Nat.maxPrimeFac n ≤ B)).card : ℝ))^2 := by
    have hsum := primeWinnerSum_low_norm_sum_le B N
    have hs : (∑ p ∈ L, ‖primeWinnerSum p N‖^2) ≤
        (∑ p ∈ L, ‖primeWinnerSum p N‖)^2 :=
      sum_sq_le_sq_sum_of_nonneg (fun p _ => norm_nonneg (primeWinnerSum p N))
    simp only [Real.norm_eq_abs, sq_abs] at hs
    exact hs.trans (pow_le_pow_left₀ (sum_nonneg (fun _ _ => norm_nonneg _)) hsum 2)
  have hH : (∑ p ∈ H, (primeWinnerSum p N)^2) ≤
      (2 * (N : ℝ) / (B+1) + 1) * N := by
    have hsum : (∑ p ∈ H, ‖primeWinnerSum p N‖) ≤ N :=
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => norm_nonneg _)).trans
        (primeWinnerSum_norm_sum_le N)
    calc
      _ ≤ ∑ p ∈ H, (2 * (N : ℝ) / (B+1) + 1) * ‖primeWinnerSum p N‖ := by
        apply sum_le_sum
        intro p hp
        have h := mul_le_mul_of_nonneg_right
          (primeWinnerSum_high_norm_bound B p N (mem_filter.mp hp).2)
          (norm_nonneg (primeWinnerSum p N))
        simpa only [← sq, Real.norm_eq_abs, sq_abs] using h
      _ = (2 * (N : ℝ) / (B+1) + 1) * (∑ p ∈ H, ‖primeWinnerSum p N‖) :=
        (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  rw [he]
  exact add_le_add hL hH

lemma primeWinnerEnergy_bulk_ratio_upper (B N : ℕ) (hN : 0 < N) :
    primeWinnerEnergy N / (N : ℝ)^2 ≤
      (((((range N).filter (fun n => Nat.maxPrimeFac n ≤ B)).card : ℝ))/N)^2 +
        2 / (B+1 : ℝ) + 1 / N := by
  have hb := div_le_div_of_nonneg_right (primeWinnerEnergy_bulk_upper B N) (sq_nonneg (N : ℝ))
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  convert hb using 1
  field_simp
  ring

/-- The full energy is subquadratic. This is much weaker than the
`N^(1+eta)` estimate that would imply the conjecture. -/
theorem primeWinnerEnergy_div_sq_tendsto_zero :
    Tendsto (fun N : ℕ => primeWinnerEnergy N / (N : ℝ)^2) atTop (nhds 0) := by
  have hB : Tendsto (fun N => (subpowerCutoff N + 1 : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp subpowerCutoff_atTop).atTop_add tendsto_const_nhds
  have ht := ((subpowerCutoff_smooth_count_tendsto_zero.pow 2).add
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2)).div_atTop hB)).add
      tendsto_one_div_atTop_nhds_zero_nat
  norm_num only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero] at ht
  apply squeeze_zero' _ _ ht
  · exact Eventually.of_forall fun N => by unfold primeWinnerEnergy; positivity
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact primeWinnerEnergy_bulk_ratio_upper (subpowerCutoff N) N hN

#print axioms primeWinnerEnergy_bulk_upper
#print axioms primeWinnerEnergy_div_sq_tendsto_zero
end Erdos371
