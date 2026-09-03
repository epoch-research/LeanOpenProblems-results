import Submission.FixedPrimeAvoidance

/-! Every fixed prime-avoidance indicator is a natural-mean L1 limit of its
finite-prime truncations. There is no uniformity in the forbidden prime set. -/
namespace Erdos371.FixedPrimeAvoidance
open Finset Filter FiniteSieve
open scoped Topology
attribute [local instance] Classical.propDecidable

lemma finiteAvoid_count_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    |(∑ n ∈ range N, finiteAvoid S n)-N*(∏ p ∈ S, (1-(1 : ℝ)/p))| ≤ ∏ p ∈ S, (p : ℝ) := by
  let R : ℕ → Finset ℕ := fun p => (range p).erase 0
  have hc : (↑S : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact ((hS p hp).coprime_iff_not_dvd).mpr (by
      intro hd
      have := (Nat.prime_dvd_prime_iff_eq (hS p hp) (hS q hq)).mp hd
      exact hpq this)
  have hr (p : ℕ) (hp : p ∈ S) (n : ℕ) : n % p ∈ R p ↔ ¬p ∣ n := by
    simp [R,mem_erase,mem_range,Nat.mod_lt n (hS p hp).pos,Nat.dvd_iff_mod_eq_zero]
  have hd (p : ℕ) (hp : p ∈ S) : (R p).card / (p : ℝ) = 1-(1 : ℝ)/p := by
    have hp0 := (hS p hp).pos
    have hpr : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
    simp only [R,card_erase_of_mem (mem_range.mpr hp0),card_range,Nat.cast_sub (by omega : 1 ≤ p),Nat.cast_one]
    field_simp
  have he := intersectionCount_residue_error S id R (fun p hp => (hS p hp).ne_zero) hc
    (fun p _ => erase_subset 0 (range p)) N
  have hh : intersectionCount (range N) (fun p n => n % id p ∈ R p) S =
      ((range N).filter fun n => ∀ p ∈ S, ¬p ∣ n).card := by
    unfold intersectionCount
    congr 1
    ext n
    simp only [mem_filter]
    exact and_congr_right (fun _ => forall₂_congr (fun p hp => hr p hp n))
  rw [hh] at he
  dsimp only [id_eq] at he
  have hprod : (∏ p ∈ S, (R p).card / (p : ℝ)) = ∏ p ∈ S, (1-(1 : ℝ)/p) :=
    prod_congr rfl hd
  rw [hprod] at he
  simpa [finiteAvoid] using he

lemma finiteAvoid_mean_tendsto (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, finiteAvoid S n)/N) atTop
      (𝓝 (∏ p ∈ S, (1-(1 : ℝ)/p))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
    (tendsto_const_div_atTop_nhds_zero_nat (∏ p ∈ S, (p : ℝ)))
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (∑ n ∈ range N, finiteAvoid S n)/N-(∏ p ∈ S, (1-(1 : ℝ)/p)) =
      ((∑ n ∈ range N, finiteAvoid S n)-N*(∏ p ∈ S, (1-(1 : ℝ)/p)))/N := by field_simp
  rw [Real.norm_eq_abs,he,abs_div,abs_of_pos (by exact_mod_cast hN : (0 : ℝ) < N)]
  exact div_le_div_of_nonneg_right (finiteAvoid_count_error S hS N) (Nat.cast_nonneg N)

lemma finiteAvoid_density_exp_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, (1-(1 : ℝ)/p)) ≤ Real.exp (-(∑ p ∈ S, (1 : ℝ)/p)) := by
  rw [← sum_neg_distrib,Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hS p hp).one_lt.le
    exact sub_nonneg.mpr ((one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp1).trans_eq (by norm_num))
  · intro p _
    exact Real.one_sub_le_exp_neg _

lemma positive_sum_le_prefix_add_one (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n ∧ u n ≤ 1) (N : ℕ) :
    (∑ n ∈ range N, u (n+1)) ≤ (∑ n ∈ range N, u n)+1 := by
  have he := sum_range_succ' u N
  rw [sum_range_succ] at he
  linarith [(hu 0).1,(hu N).2]

lemma prefix_sum_le_positive_add_one (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n ∧ u n ≤ 1) (N : ℕ) :
    (∑ n ∈ range N, u n) ≤ (∑ n ∈ range N, u (n+1))+1 := by
  have he := sum_range_succ' u N
  rw [sum_range_succ] at he
  linarith [(hu N).1,(hu 0).2]

lemma cut_L1_eventually_small_of_summable (B : Set ℕ) (hB : Summable (reciprocal B))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K, ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, |avoid B n-finiteAvoid (primeCut B K) n|)/N < ε := by
  have ht := hB.hasSum.tendsto_sum_nat
  obtain ⟨K,hK⟩ := (ht.eventually (lt_mem_nhds (show (∑' p, reciprocal B p)-ε/2 < ∑' p, reciprocal B p by linarith))).exists
  refine ⟨K,?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const (by positivity : (0 : ℝ) < ε/2)] with N hN hsmall
  have hp := cut_error_bound_of_summable B hB K N
  have he := prefix_sum_le_positive_add_one
    (fun n => finiteAvoid (primeCut B K) n-avoid B n) (cut_error_bounds B K) N
  simp_rw [← cut_error_eq_abs] at he
  have hb := div_le_div_of_nonneg_right (he.trans (add_le_add hp le_rfl)) (Nat.cast_nonneg N)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [add_div,mul_div_cancel_left₀ _ hNr] at hb
  linarith

lemma exists_cut_large_reciprocal (B : Set ℕ) (hB : ¬Summable (reciprocal B)) (T : ℝ) :
    ∃ K, T < ∑ p ∈ primeCut B K, (1 : ℝ)/p := by
  by_contra h
  push_neg at h
  have hbound (S : Finset ℕ) : (∑ p ∈ S, reciprocal B p) ≤ T := by
    let K := S.sup id + 1
    calc
      _ ≤ ∑ p ∈ range K, reciprocal B p := sum_le_sum_of_subset_of_nonneg
        (fun p hp => mem_range.mpr (by dsimp [K]; have ht := Finset.le_sup (f := id) hp; simp only [id_eq] at ht; omega))
        (fun p _ _ => reciprocal_nonneg B p)
      _ ≤ T := by rw [← cut_reciprocal_sum]; exact h K
  exact hB (summable_of_sum_le (reciprocal_nonneg B) hbound)

lemma cut_L1_eventually_small_of_not_summable (B : Set ℕ) (hB : ¬Summable (reciprocal B))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K, ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, |avoid B n-finiteAvoid (primeCut B K) n|)/N < ε := by
  obtain ⟨K,hK⟩ := exists_cut_large_reciprocal B hB (-Real.log ε)
  have hd : (∏ p ∈ primeCut B K, (1-(1 : ℝ)/p)) < ε := by
    apply (finiteAvoid_density_exp_bound _ (fun p hp => (mem_filter.mp hp).2.1)).trans_lt
    rw [← Real.exp_log hε]
    exact Real.exp_lt_exp.mpr (by linarith)
  have ht := finiteAvoid_mean_tendsto (primeCut B K) (fun p hp => (mem_filter.mp hp).2.1)
  refine ⟨K,?_⟩
  filter_upwards [ht.eventually_lt_const hd] with N hN
  apply lt_of_le_of_lt _ hN
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply sum_le_sum
  intro n _
  rw [cut_error_eq_abs]
  exact sub_le_self _ (avoid_bounds B n).1

/-- The truncation is allowed to depend on the entire fixed forbidden set.
This quantifier is essential for applications to moving smoothness cutoffs. -/
theorem fixed_avoidance_L1_approximation (B : Set ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K, ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, |avoid B n-finiteAvoid (primeCut B K) n|)/N < ε := by
  by_cases hB : Summable (reciprocal B)
  · exact cut_L1_eventually_small_of_summable B hB ε hε
  · exact cut_L1_eventually_small_of_not_summable B hB ε hε

#print axioms fixed_avoidance_L1_approximation
end Erdos371.FixedPrimeAvoidance
