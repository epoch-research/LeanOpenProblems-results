import FormalConjecturesUtil
import Submission.EuclideanCompression
import Submission.SubpowerSeparation

/-! The Euclidean residue compression has sublinear range in density.
Consequently no bounded-fiber restriction of this particular compression
can have positive density. This is not a comparison-density theorem. -/

namespace Erdos371CompressionRangeCollapse

open Finset Filter Erdos371PrimeDiscrepancy Erdos371EuclideanCompression
open scoped Topology

attribute [local instance] Classical.propDecidable

noncomputable def count (p : ℕ → Prop) (N : ℕ) : ℝ :=
  ((Finset.range N).filter p).card

lemma count_eq (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    count p N = (((range N).filter p).card : ℝ) := by
  unfold count
  congr 1
  apply congrArg Finset.card
  ext n
  simp only [mem_filter]

def reduce (n : ℕ) : ℕ :=
  if P n < P (n+1) then ascend n else descend n

def loser (n : ℕ) : ℕ := min (P n) (P (n+1))

lemma P_pos {n : ℕ} (hn : 0 < n) : 0 < P n := by
  by_cases he : n = 1
  · simp [he,P]
  · exact (Nat.prime_maxPrimeFac_of_one_lt n (by omega)).pos

lemma descend_weight_bound (n : ℕ) : descend n * P n ≤ n * P (n+1) := by
  have hr : P n % P (n+1) ≤ P (n+1) := (Nat.mod_lt _ (P_pos (by omega))).le
  have hc : descend n ≤ (n / P n) * P (n+1) :=
    Nat.mul_le_mul (Nat.mod_le _ _) hr
  calc
    _ ≤ ((n / P n) * P (n+1)) * P n := Nat.mul_le_mul_right _ hc
    _ = n * P (n+1) := by
      rw [mul_right_comm, Nat.div_mul_cancel Nat.maxPrimeFac_dvd]

lemma ascend_weight_bound (n : ℕ) : ascend n * P (n+1) ≤ (n+1) * P n := by
  by_cases hn : n = 0
  · subst n; decide +kernel
  have hc : ascend n ≤ ((n+1) / P (n+1)) * P n := by
    apply (Nat.sub_le _ _).trans
    exact Nat.mul_le_mul (Nat.mod_le _ _) (Nat.mod_lt _ (P_pos (Nat.pos_of_ne_zero hn))).le
  calc
    _ ≤ (((n+1) / P (n+1)) * P n) * P (n+1) := Nat.mul_le_mul_right _ hc
    _ = (n+1) * P n := by
      rw [mul_right_comm, Nat.div_mul_cancel Nat.maxPrimeFac_dvd]

lemma reduce_weight_bound (n : ℕ) : reduce n * winner n ≤ (n+1) * loser n := by
  unfold reduce winner loser
  split_ifs with h
  · rw [max_eq_right h.le, min_eq_left h.le]
    exact ascend_weight_bound n
  · have hle : P (n+1) ≤ P n := by omega
    rw [max_eq_left hle, min_eq_right hle]
    exact (descend_weight_bound n).trans (Nat.mul_le_mul_right _ (by omega))

lemma comparable_of_large_output {n K : ℕ} (hn : 0 < n)
    (h : n ≤ K * reduce n) : winner n ≤ (2*K) * loser n := by
  have h₁ := Nat.mul_le_mul_right (winner n) h
  have h₂ := Nat.mul_le_mul_left K (reduce_weight_bound n)
  have h₃ : K * ((n+1) * loser n) ≤ n * ((2*K) * loser n) := by
    have hh := Nat.mul_le_mul_right (K * loser n) (show n+1 ≤ 2*n by omega)
    nlinarith
  have hh : n * winner n ≤ n * ((2*K) * loser n) := by nlinarith
  exact Nat.le_of_mul_le_mul_left hh hn

lemma constant_ratio_hasDensity_zero (K : ℕ) :
    {n | winner n ≤ K * loser n}.HasDensity 0 := by
  apply Erdos371SubpowerSeparation.subpower_hasDensity_zero_of_log (fun _ => K)
  exact tendsto_const_nhds.div_atTop
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

lemma exceptional_card_bound (K N : ℕ) :
    ((range N).filter (fun n => n ≤ K * reduce n)).card ≤
      1 + ((range N).filter (fun n => winner n ≤ (2*K) * loser n)).card := by
  have hs : (range N).filter (fun n => n ≤ K * reduce n) ⊆
      {0} ∪ (range N).filter (fun n => winner n ≤ (2*K) * loser n) := by
    intro n hn
    obtain ⟨hnN, hn⟩ := mem_filter.mp hn
    by_cases hz : n = 0
    · simp [hz]
    · exact mem_union_right _ (mem_filter.mpr
        ⟨hnN, comparable_of_large_output (Nat.pos_of_ne_zero hz) hn⟩)
  exact (card_le_card hs).trans (by
    simpa using card_union_le ({0} : Finset ℕ)
      ((range N).filter (fun n => winner n ≤ (2*K) * loser n)))

/-- Outside a density-zero set, the reduction beats each fixed linear factor. -/
theorem exceptional_hasDensity_zero (K : ℕ) :
    {n | n ≤ K * reduce n}.HasDensity 0 := by
  have hc := constant_ratio_hasDensity_zero (2*K)
  change Tendsto _ atTop (𝓝 0) at hc ⊢
  simp only [Erdos371ReflectionRange.partialDensity_eq_filter_card, Set.mem_setOf_eq] at hc ⊢
  have ht := tendsto_one_div_atTop_nhds_zero_nat.add hc
  simp only [zero_add] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
  · intro N; positivity
  · intro N
    have h := div_le_div_of_nonneg_right
      (Nat.cast_le (α := ℝ) |>.mpr (exceptional_card_bound K N)) (Nat.cast_nonneg N)
    simpa only [Nat.cast_add, Nat.cast_one, add_div, ← count_eq] using h

/-- A fiber bound on finite prefixes, so that infinite fibers cannot be
mistaken for fibers of cardinality zero. -/
def BoundedFibersOn (f : ℕ → ℕ) (A : Set ℕ) (C : ℕ) : Prop :=
  ∀ N m : ℕ, ((range N).filter (fun n => n ∈ A ∧ f n = m)).card ≤ C

lemma bounded_fiber_count {f : ℕ → ℕ} {A : Set ℕ} {C : ℕ}
    (hC : BoundedFibersOn f A C) {K : ℕ} (hK : 0 < K) (N : ℕ) :
    ((range N).filter (fun n => n ∈ A)).card ≤
      ((range N).filter (fun n => n ≤ K * f n)).card + C * (N/K+1) := by
  let E := (range N).filter (fun n => n ≤ K * f n)
  let B := (range (N/K+1)).biUnion
    (fun m => (range N).filter (fun n => n ∈ A ∧ f n = m))
  have hs : (range N).filter (fun n => n ∈ A) ⊆ E ∪ B := by
    intro n hn
    obtain ⟨hnN, hnA⟩ := mem_filter.mp hn
    by_cases he : n ≤ K * f n
    · exact mem_union_left _ (mem_filter.mpr ⟨hnN,he⟩)
    · apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨f n, mem_range.mpr ?_, mem_filter.mpr ⟨hnN,hnA,rfl⟩⟩
      have hfn : f n ≤ N/K := (Nat.le_div_iff_mul_le hK).mpr (by
        have := mem_range.mp hnN
        nlinarith)
      omega
  have hb : B.card ≤ C * (N/K+1) := by
    apply card_biUnion_le.trans
    calc
      _ ≤ ∑ _m ∈ range (N/K+1), C := sum_le_sum (fun m _ => hC N m)
      _ = C * (N/K+1) := by simp [mul_comm]
  exact (card_le_card hs).trans ((card_union_le E B).trans (Nat.add_le_add_left hb _))

/-- General counting principle: a map that shrinks almost every input by
any prescribed fixed factor cannot have bounded fibers on a positive-density set. -/
theorem density_zero_of_compression {f : ℕ → ℕ}
    (hf : ∀ K : ℕ, {n | n ≤ K * f n}.HasDensity 0)
    {A : Set ℕ} {C : ℕ} (hC : BoundedFibersOn f A C) : A.HasDensity 0 := by
  change Tendsto _ atTop (𝓝 0)
  simp only [Erdos371ReflectionRange.partialDensity_eq_filter_card]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlim : Tendsto (fun K : ℕ => (C:ℝ)/K) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  obtain ⟨K,hK,hfrac⟩ := ((eventually_gt_atTop 0).and
    (hlim.eventually_lt_const (half_pos hε))).exists
  have he := hf K
  change Tendsto _ atTop (𝓝 0) at he
  simp only [Erdos371ReflectionRange.partialDensity_eq_filter_card, Set.mem_setOf_eq] at he
  have ht := (he.add hlim).eventually_lt_const (show (0:ℝ)+0 < ε/2 by linarith)
  filter_upwards [ht, eventually_gt_atTop 0] with N htN hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have hc : (((range N).filter (fun n => n ∈ A)).card:ℝ) ≤
      (((range N).filter (fun n => n ≤ K * f n)).card:ℝ) +
        (C:ℝ)*((N/K:ℕ)+1) := by
    exact_mod_cast bounded_fiber_count hC hK N
  have hdiv : ((N/K:ℕ):ℝ) ≤ (N:ℝ)/K := Nat.cast_div_le
  have hNN : (N:ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hKK : (K:ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
  have hu : (((range N).filter (fun n => n ∈ A)).card:ℝ)/N ≤
      (((range N).filter (fun n => n ≤ K * f n)).card:ℝ)/N + (C:ℝ)/N + (C:ℝ)/K := by
    calc
      _ ≤ ((((range N).filter (fun n => n ≤ K * f n)).card:ℝ) +
          (C:ℝ)*((N:ℝ)/K+1))/N :=
        div_le_div_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α := ℝ) C])
          (Nat.cast_nonneg N)
      _ = _ := by field_simp; ring
  simp only [← count_eq] at htN hu ⊢
  linarith

theorem bounded_fiber_restriction_hasDensity_zero {A : Set ℕ} {C : ℕ}
    (hC : BoundedFibersOn reduce A C) : A.HasDensity 0 :=
  density_zero_of_compression exceptional_hasDensity_zero hC

/-- In particular, discarding a density-zero set cannot make this map injective. -/
theorem injective_restriction_hasDensity_zero {A : Set ℕ}
    (hA : Set.InjOn reduce A) : A.HasDensity 0 := by
  apply bounded_fiber_restriction_hasDensity_zero (C := 1)
  intro N m
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨_, haA, ham⟩ := Finset.mem_filter.mp ha
  obtain ⟨_, hbA, hbm⟩ := Finset.mem_filter.mp hb
  exact hA haA hbA (ham.trans hbm.symm)

end Erdos371CompressionRangeCollapse

#print axioms Erdos371CompressionRangeCollapse.exceptional_hasDensity_zero
#print axioms Erdos371CompressionRangeCollapse.bounded_fiber_restriction_hasDensity_zero

#print axioms Erdos371CompressionRangeCollapse.injective_restriction_hasDensity_zero
