import FormalConjecturesUtil
import Submission.CompleteAdditiveComparison

/-! Proper compression to a smaller adjacent divisor pair cannot preserve both
largest prime factors on a positive-density set. This is a limitation of a
particular proposed proof strategy, not a disproof of Erdős 371. -/

namespace Erdos371AdjacentDivisorCompression

open Finset Filter Erdos371PrimeDiscrepancy Erdos371BoundedPrimeGap
open Erdos371ReflectionRange Erdos371CompleteAdditiveComparison
open scoped Topology

attribute [local instance] Classical.propDecidable

lemma forward_square_bound {m n : ℕ} (hmn : m < n)
    (hm : m ∣ n) (hm1 : m+1 ∣ n+1) : m^2 ≤ n+1 := by
  have h1 : m ∣ n-m := Nat.dvd_sub hm (dvd_refl m)
  have h2 : m+1 ∣ n-m := by
    have h := Nat.dvd_sub hm1 (dvd_refl (m+1))
    simpa using h
  have h3 : m*(m+1) ∣ n-m :=
    (show m.Coprime (m+1) by simp).mul_dvd_of_dvd_of_dvd h1 h2
  have h4 := Nat.le_of_dvd (Nat.sub_pos_of_lt hmn) h3
  have h5 := Nat.sub_add_cancel hmn.le
  nlinarith

lemma reverse_square_bound {m n : ℕ} (hm : m ∣ n+1)
    (hm1 : m+1 ∣ n) : m^2 ≤ n+1 := by
  have h1 : m ∣ n+m+1 := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.dvd_add hm (dvd_refl m)
  have h2 : m+1 ∣ n+m+1 := by
    simpa [Nat.add_assoc] using Nat.dvd_add hm1 (dvd_refl (m+1))
  have h3 : m*(m+1) ∣ n+m+1 :=
    (show m.Coprime (m+1) by simp).mul_dvd_of_dvd_of_dvd h1 h2
  have h4 := Nat.le_of_dvd (by omega : 0 < n+m+1) h3
  nlinarith

/-- The weaker winner bound is necessary whenever both prime-factor values
are preserved by either orientation of the compression. -/
def compressible (n : ℕ) : Prop := ∃ m : ℕ,
  0 < m ∧ m < n ∧
    ((m ∣ n ∧ m+1 ∣ n+1) ∨ (m+1 ∣ n ∧ m ∣ n+1)) ∧ winner n ≤ m+1

noncomputable def cover (K N : ℕ) : Finset ℕ :=
  (Ico K (Nat.sqrt N+1)).biUnion fun m =>
    solutions m (m+1) N ∪ solutions (m+1) m N

lemma one_class_card_bound {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ((solutions m (m+1) N ∪ solutions (m+1) m N).card : ℝ) ≤
      2*(N:ℝ)/(m:ℝ)^2 + 2 := by
  have hc := (card_union_le (solutions m (m+1) N) (solutions (m+1) m N)).trans
    (Nat.add_le_add (solutions_card_le (show m.Coprime (m+1) by simp) N)
      (solutions_card_le (show m.Coprime (m+1) by simp).symm N))
  have hcr : ((solutions m (m+1) N ∪ solutions (m+1) m N).card : ℝ) ≤
      ((N/(m*(m+1)) : ℕ):ℝ) + 1 + (((N/((m+1)*m) : ℕ):ℝ) + 1) := by
    exact_mod_cast hc
  have hd : ((N/(m*(m+1)) : ℕ):ℝ) ≤ (N:ℝ)/((m:ℝ)*(m+1)) := by
    have h : ((N/(m*(m+1)) : ℕ):ℝ) ≤ (N:ℝ)/(m*(m+1):ℕ) := Nat.cast_div_le
    exact_mod_cast h
  have hden : (N:ℝ)/((m:ℝ)*(m+1)) ≤ (N:ℝ)/(m:ℝ)^2 := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity)
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have hswap : N/((m+1)*m) = N/(m*(m+1)) := by rw [Nat.mul_comm (m+1) m]
  rw [hswap] at hcr
  rw [mul_div_assoc]
  linarith

lemma cover_card_bound {K : ℕ} (hK : 0 < K) (N : ℕ) :
    ((cover K N).card : ℝ) ≤ 4*(N:ℝ)/K + 2*(Nat.sqrt N+1:ℕ) := by
  calc
    _ ≤ ∑ m ∈ Ico K (Nat.sqrt N+1),
        ((solutions m (m+1) N ∪ solutions (m+1) m N).card : ℝ) := by
      exact_mod_cast card_biUnion_le (s := Ico K (Nat.sqrt N+1))
        (t := fun m => solutions m (m+1) N ∪ solutions (m+1) m N)
    _ ≤ ∑ m ∈ Ico K (Nat.sqrt N+1), (2*(N:ℝ)/(m:ℝ)^2 + 2) :=
      sum_le_sum fun m hm => one_class_card_bound (hK.trans_le (mem_Ico.mp hm).1) N
    _ = 2*(N:ℝ)*(∑ m ∈ Ico K (Nat.sqrt N+1), 1/(m:ℝ)^2) +
        2*((Ico K (Nat.sqrt N+1)).card:ℝ) := by
      rw [sum_add_distrib, mul_sum]
      simp [mul_comm, div_eq_mul_inv]
    _ ≤ 2*(N:ℝ)*(2/K) + 2*(Nat.sqrt N+1:ℕ) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (Erdos371TerminalCompression.sum_reciprocal_sq hK _) (by positivity)
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Nat.cast_le.mpr (by simp)
    _ = _ := by ring

lemma compressible_count_bound {K : ℕ} (hK : 0 < K) (N : ℕ) :
    (((range N).filter compressible).card : ℝ) ≤
      (((range N).filter fun n => P n ≤ K).card : ℝ) +
        4*(N:ℝ)/K + 2*(Nat.sqrt N+1:ℕ) := by
  have hsub : (range N).filter compressible ⊆
      ((range N).filter fun n => P n ≤ K) ∪ cover K N := by
    intro n hn
    obtain ⟨hnN, m, hm0, hmn, hdiv, hwin⟩ := mem_filter.mp hn
    by_cases hmK : m < K
    · apply mem_union_left
      have hp : P n ≤ winner n := le_max_left _ _
      exact mem_filter.mpr ⟨hnN, by omega⟩
    · have hsq : m^2 ≤ n+1 := by
        rcases hdiv with h | h
        · exact forward_square_bound hmn h.1 h.2
        · exact reverse_square_bound h.2 h.1
      have hmS : m ≤ Nat.sqrt N := Nat.le_sqrt'.mpr
        (hsq.trans (by have := mem_range.mp hnN; omega))
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨m, mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
      rcases hdiv with h | h
      · exact mem_union_left _ (mem_filter.mpr ⟨hnN, h⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hnN, h⟩)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hcr : (((range N).filter compressible).card : ℝ) ≤
      (((range N).filter fun n => P n ≤ K).card : ℝ) + (cover K N).card := by
    exact_mod_cast hc
  linarith [cover_card_bound hK N]

lemma compressible_density_bound {K : ℕ} (hK : 0 < K) {N : ℕ} (hN : 0 < N) :
    {n | compressible n}.partialDensity Set.univ N ≤
      {n | P n ≤ K}.partialDensity Set.univ N + 4/K +
        2*(Real.sqrt N + 1)/N := by
  rw [Erdos371Exploration.partialDensity_eq_count,
    Erdos371Exploration.partialDensity_eq_count]
  have hh := div_le_div_of_nonneg_right (compressible_count_bound hK N) (Nat.cast_nonneg (α := ℝ) N)
  have hs : (Nat.sqrt N+1:ℕ) ≤ Real.sqrt N+1 := by
    push_cast
    linarith [Real.nat_sqrt_le_real_sqrt (a := N)]
  have hu : (((range N).filter (fun n => P n ≤ K)).card : ℝ)/(N:ℝ) + 4/(K:ℝ) +
      2*((Nat.sqrt N+1:ℕ):ℝ)/N ≤
      (((range N).filter (fun n => P n ≤ K)).card : ℝ)/(N:ℝ) + 4/(K:ℝ) +
      2*(Real.sqrt N+1)/N := by
    have hf := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (show (0:ℝ) ≤ 2 by norm_num)) (Nat.cast_nonneg (α := ℝ) N)
    linarith
  apply le_trans _ hu
  convert hh using 1
  field_simp


/-- Almost no input has a proper adjacent divisor compression whose target is
large enough to preserve the winning prime. -/
theorem compressible_hasDensity_zero : {n | compressible n}.HasDensity 0 := by
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt N / N) atTop (𝓝 0) := by
    simp_rw [Real.sqrt_div_self]
    exact tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have htail : Tendsto (fun N : ℕ => 2*(Real.sqrt N+1)/N) atTop (𝓝 0) := by
    simpa [mul_div_assoc, add_div] using
      (hsqrt.add tendsto_one_div_atTop_nhds_zero_nat).const_mul 2
  rw [Set.HasDensity, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hKbig⟩ := exists_nat_gt (8/ε)
  have hK : 0 < K := Nat.cast_pos.mp ((by positivity : (0:ℝ) < 8/ε).trans hKbig)
  have hsmall : 4/(K:ℝ) < ε/2 := by
    have hk : (0:ℝ) < K := Nat.cast_pos.mpr hK
    have hh := (div_lt_iff₀ hε).mp hKbig
    apply (div_lt_iff₀ hk).mpr
    nlinarith
  have hlow := Erdos371Exploration.bounded_maxPrimeFac_hasDensity_zero K
  have hu := hlow.add htail
  simp only [add_zero] at hu
  filter_upwards [hu.eventually_lt_const (half_pos hε), eventually_gt_atTop 0]
    with N huN hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (show
    0 ≤ {n | compressible n}.partialDensity Set.univ N by unfold Set.partialDensity; positivity)]
  have hb := compressible_density_bound hK hN
  change {n | P n ≤ K}.partialDensity Set.univ N + 2*(Real.sqrt N+1)/N < ε/2 at huN
  linarith

/-- The two possible orientations of a divisorwise reduction preserving both
largest prime factors. The target is required to be strictly smaller. -/
def preserving (n : ℕ) : Prop := ∃ m : ℕ, 0 < m ∧ m < n ∧
  ((m ∣ n ∧ m+1 ∣ n+1 ∧ P n = P m ∧ P (n+1) = P (m+1)) ∨
   (m+1 ∣ n ∧ m ∣ n+1 ∧ P n = P (m+1) ∧ P (n+1) = P m))

lemma preserving_subset : {n | preserving n} ⊆ {n | compressible n} := by
  intro n hn
  obtain ⟨m, hm, hmn, h | h⟩ := hn
  · refine ⟨m, hm, hmn, Or.inl ⟨h.1, h.2.1⟩, ?_⟩
    rw [winner, h.2.2.1, h.2.2.2]
    exact max_le (Nat.maxPrimeFac_le.trans (by omega)) Nat.maxPrimeFac_le
  · refine ⟨m, hm, hmn, Or.inr ⟨h.1, h.2.1⟩, ?_⟩
    rw [winner, h.2.2.1, h.2.2.2]
    exact max_le Nat.maxPrimeFac_le (Nat.maxPrimeFac_le.trans (by omega))

/-- A density-zero obstruction to the proposed divisorwise compression. This
is not a negation of the Erdős density conjecture. -/
theorem preserving_hasDensity_zero : {n | preserving n}.HasDensity 0 :=
  Erdos371Exploration.density_zero_of_subset preserving_subset compressible_hasDensity_zero

end Erdos371AdjacentDivisorCompression

#print axioms Erdos371AdjacentDivisorCompression.compressible_density_bound
#print axioms Erdos371AdjacentDivisorCompression.compressible_hasDensity_zero
#print axioms Erdos371AdjacentDivisorCompression.preserving_hasDensity_zero
