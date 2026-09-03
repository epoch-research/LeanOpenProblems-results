import FormalConjecturesUtil
import Submission.ProductSignTransport
import Submission.SmoothDensity
import Submission.LogSmoothCount

/-! Same-winner product transport cannot act on a positive proportion of the
inputs while keeping its output in a fixed linear range. This is an obstruction
to that particular transport, not a disproof of Erdős 371. -/

namespace Erdos371LinearProductTransportObstruction

open Finset Filter Erdos371PrimeDiscrepancy Erdos371ProductSignTransport
open scoped Topology

lemma small_partner_bound {n m H : ℕ} (hm : m < H)
    (hw : winner n = winner m) : P n ≤ H := by
  exact (le_max_left _ _).trans (hw ▸ winner_le hm)

lemma small_partner_iff {n H : ℕ} (hn : 0 < n) :
    (∃ m < H, winner n = winner m) ↔ winner n ≤ H := by
  constructor
  · rintro ⟨m, hm, hw⟩
    exact hw ▸ winner_le hm
  · intro h
    let p := winner n
    have hp : p.Prime := winner_prime hn
    have he : p-1+1=p := Nat.sub_add_cancel hp.one_lt.le
    have htop : winner (p-1)=p := by
      unfold winner P
      rw [he, hp.maxPrimeFac_eq_self]
      exact max_eq_right (Nat.maxPrimeFac_le.trans (Nat.sub_le _ _))
    exact ⟨p-1, by dsimp [p] at *; omega, htop.symm⟩

lemma fixed_small_partner_density_zero (H : ℕ) :
    {n | ∃ m < H, winner n = winner m}.HasDensity 0 := by
  apply Erdos371Exploration.density_zero_of_subset _
    (Erdos371Exploration.bounded_maxPrimeFac_hasDensity_zero H)
  rintro n ⟨m, hm, hw⟩
  exact small_partner_bound hm hw

lemma moving_small_partner_count_zero (H : ℕ → ℕ)
    (hH : ∀ᶠ N in atTop, 0 < H N)
    (hlog : Tendsto (fun N : ℕ => Real.log (H N : ℝ)/Real.log (N:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (((range N).filter (fun n => ∃ m < H N, winner n=winner m)).card:ℝ)/N)
      atTop (𝓝 0) := by
  classical
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (Erdos371LogSmoothCount.moving_smooth_count_tendsto_zero H hH hlog)
  · intro N
    positivity
  · intro N
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro n hn
    obtain ⟨hnN, m, hm, hw⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hnN, small_partner_bound hm hw⟩

lemma product_le_transport_add_one (n m : ℕ) :
    n*m ≤ transport n m+1 := by
  have h := Nat.mul_le_mul (lower_bounds n).1 (lower_bounds m).1
  unfold transport
  split_ifs <;> omega

/-- A source away from the beginning of the interval can have a linearly
bounded output only if its common winning prime is bounded. -/
lemma winner_bound_of_linear_output {n m N C K : ℕ} (hn : 0 < n)
    (hN : N ≤ K*n) (hw : winner n=winner m)
    (hout : transport n m ≤ C*N) : winner n ≤ C*K+2 := by
  have hnm : n*m ≤ C*N+1 := (product_le_transport_add_one n m).trans (by omega)
  have hCN : C*N ≤ C*(K*n) := Nat.mul_le_mul_left C hN
  have hm : m ≤ C*K+1 := by
    by_contra h
    have hmul := Nat.mul_le_mul_left n (show C*K+2 ≤ m by omega)
    nlinarith
  have hwin : winner m ≤ m+1 := winner_le (by omega)
  omega

noncomputable def linearSources (C N : ℕ) : Finset ℕ := by
  classical
  exact (range N).filter (fun n => ∃ m, 1 < m ∧ winner n=winner m ∧ transport n m ≤ C*N)

lemma linear_sources_count_bound (C N : ℕ) {K : ℕ} (hK : 0 < K) :
    (linearSources C N).card ≤ N/K+1 +
      ((range N).filter (fun n => P n ≤ C*K+2)).card := by
  classical
  have hsub : linearSources C N ⊆ range (N/K+1) ∪
      (range N).filter (fun n => P n ≤ C*K+2) := by
    intro n hn
    change n ∈ (range N).filter _ at hn
    obtain ⟨hnN, m, _, hw, hout⟩ := mem_filter.mp hn
    by_cases hs : K*n < N
    · apply mem_union_left
      apply mem_range.mpr
      have hh : n ≤ N/K := (Nat.le_div_iff_mul_le hK).mpr (by nlinarith)
      omega
    · apply mem_union_right
      apply mem_filter.mpr ⟨hnN, ?_⟩
      have hn0 : 0 < n := by
        have := mem_range.mp hnN
        nlinarith
      exact (le_max_left _ _).trans
        (winner_bound_of_linear_output hn0 (by omega) hw hout)
  exact (Finset.card_le_card hsub).trans (by
    simpa only [card_range] using Finset.card_union_le
      (range (N/K+1)) ((range N).filter (fun n => P n ≤ C*K+2)))

/-- For every fixed output-range constant, the source population admitting
a same-winner product transport into that range has asymptotic proportion zero.
This gives no cancellation estimate for the original comparison sequence. -/
theorem linear_sources_proportion_zero (C : ℕ) :
    Tendsto (fun N : ℕ => ((linearSources C N).card:ℝ)/N) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hK, hfrac⟩ := ((eventually_gt_atTop 0).and
    (tendsto_one_div_atTop_nhds_zero_nat.eventually_lt_const
      (show (0:ℝ) < ε/2 by positivity))).exists
  have hs : Tendsto (fun N : ℕ =>
      (((range N).filter (fun n => P n ≤ C*K+2)).card:ℝ)/N) atTop (𝓝 0) := by
    simpa only [Set.HasDensity, Erdos371Exploration.bounded_maxPrimeFac_partialDensity] using
      Erdos371Exploration.bounded_maxPrimeFac_hasDensity_zero (C*K+2)
  have htail := (tendsto_one_div_atTop_nhds_zero_nat.add hs).eventually_lt_const
    (show (0:ℝ)+0 < ε/2 by linarith)
  filter_upwards [htail, eventually_gt_atTop 0] with N ht hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have hc : ((linearSources C N).card:ℝ) ≤
      (N/K:ℕ)+1+(((range N).filter (fun n => P n ≤ C*K+2)).card:ℝ) := by
    exact_mod_cast linear_sources_count_bound C N hK
  have hdiv : ((N/K:ℕ):ℝ) ≤ (N:ℝ)/K := Nat.cast_div_le
  have hNN : (N:ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hu : ((linearSources C N).card:ℝ)/N ≤ 1/(K:ℝ) +
      (1/(N:ℝ)+(((range N).filter (fun n => P n ≤ C*K+2)).card:ℝ)/N) := by
    calc
      _ ≤ ((N:ℝ)/K+1+(((range N).filter (fun n => P n ≤ C*K+2)).card:ℝ))/N :=
        div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg N)
      _ = _ := by
        have hKK : (K:ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
        field_simp
        ring
  linarith

end Erdos371LinearProductTransportObstruction

#print axioms Erdos371LinearProductTransportObstruction.small_partner_iff
#print axioms Erdos371LinearProductTransportObstruction.moving_small_partner_count_zero
#print axioms Erdos371LinearProductTransportObstruction.linear_sources_proportion_zero
