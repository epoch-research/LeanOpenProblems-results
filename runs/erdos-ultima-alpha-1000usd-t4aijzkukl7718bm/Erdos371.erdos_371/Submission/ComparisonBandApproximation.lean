import Submission.ComparisonBoxBands

/-! Fixed power-sized lower and upper box cutoffs retain arbitrarily close to
all comparison mass. Signed cancellation is not proved here. -/
namespace Erdos371
open Finset Filter RandomBins FiniteSieve
open scoped Topology
attribute [local instance] Classical.propDecidable

lemma allocationAvoidanceBase_bounds (K : ℕ) (hK : 0 < K) :
    0 ≤ 1-1/(K : ℝ) ∧ 1-1/(K : ℝ) < 1 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hK1
  norm_num only [div_one] at hi
  exact ⟨sub_nonneg.mpr hi,sub_lt_self _ (one_div_pos.mpr hKr)⟩

lemma comparisonBandAllocationWeight_point_bound (K N n : ℕ) (hK : 0 < K)
    (η α : ℝ) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ (N : ℝ)^η ≤ q ∧ (q : ℝ) ≤ (N : ℝ)^α) :
    comparisonAllocationWeight K N 0 n-comparisonBandAllocationWeight K N η n ≤
      (if n < 2 then (1 : ℝ) else 0) +
      (if (primeWinner n : ℝ) ≤ (N : ℝ)^α then 1 else 0) +
      (K : ℝ)*((1-1/(K : ℝ))^primeDivisorCountIn S n +
        (1-1/(K : ℝ))^primeDivisorCountIn S (n+1)) := by
  have hW := comparisonAllocationWeight_mem_unit K N hK 0 n
  have hB := comparisonBandAllocationWeight_bounds K N hK η n
  have hr := (allocationAvoidanceBase_bounds K hK).1
  have htail : 0 ≤ (K : ℝ)*((1-1/(K : ℝ))^primeDivisorCountIn S n +
        (1-1/(K : ℝ))^primeDivisorCountIn S (n+1)) := by positivity
  by_cases hbad : n < 2 ∨ (primeWinner n : ℝ) ≤ (N : ℝ)^α
  · have hI : (1 : ℝ) ≤ (if n < 2 then 1 else 0) +
        (if (primeWinner n : ℝ) ≤ (N : ℝ)^α then 1 else 0) := by
      split_ifs <;> norm_num <;> tauto
    linarith
  · push_neg at hbad
    obtain ⟨hn,hp⟩ := hbad
    simpa only [if_neg (by omega : ¬n < 2),if_neg (not_le_of_gt hp),zero_add] using
      comparisonBandAllocationWeight_prime_count_bound K N n hK η α S hS (by omega) hp

lemma comparisonBandAllocationWeight_mean_loss_bound (K N : ℕ) (hK : 0 < K) (hN : 0 < N)
    (η α : ℝ) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ (N : ℝ)^η ≤ q ∧ (q : ℝ) ≤ (N : ℝ)^α) :
    (∑ n ∈ range N, (comparisonAllocationWeight K N 0 n-comparisonBandAllocationWeight K N η n))/N ≤
      (2+(K : ℝ))/N +
      (((range N).filter fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^α).card : ℝ)/N +
      2*(K : ℝ)*((∑ n ∈ range N, (1-1/(K : ℝ))^primeDivisorCountIn S (n+1))/N) := by
  have hs := sum_le_sum (s := range N) fun n hn =>
    comparisonBandAllocationWeight_point_bound K N n hK η α S hS
  simp only [sum_add_distrib,← mul_sum] at hs
  have hsmall : (∑ n ∈ range N, if n < 2 then (1 : ℝ) else 0) ≤ 2 := by
    have hc : ((range N).filter fun n => n < 2).card ≤ 2 := by
      apply (card_le_card _).trans_eq (card_range 2)
      intro n hn
      exact mem_range.mpr (mem_filter.mp hn).2
    simpa using (Nat.cast_le (α := ℝ)).mpr hc
  have hlow : (∑ n ∈ range N, if (primeWinner n : ℝ) ≤ (N : ℝ)^α then (1 : ℝ) else 0) ≤
      (((range N).filter fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^α).card : ℝ) := by
    have hc : ((range N).filter fun n => (primeWinner n : ℝ) ≤ (N : ℝ)^α) ⊆
        ((range N).filter fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^α) := by
      intro n hn
      obtain ⟨hn,hp⟩ := mem_filter.mp hn
      have hle : Nat.maxPrimeFac (n+1) ≤ primeWinner n := le_max_right _ _
      exact mem_filter.mpr ⟨hn,(show (Nat.maxPrimeFac (n+1) : ℝ) ≤ primeWinner n by
        exact_mod_cast hle).trans hp⟩
    simpa using (Nat.cast_le (α := ℝ)).mpr (card_le_card hc)
  let f : ℕ → ℝ := fun n => (1-1/(K : ℝ))^primeDivisorCountIn S n
  have hr := allocationAvoidanceBase_bounds K hK
  have hshift : (∑ n ∈ range N, f n) ≤ (∑ n ∈ range N, f (n+1))+1 := by
    have he := sum_range_succ' f N
    rw [sum_range_succ] at he
    have h0 : f 0 ≤ 1 := pow_le_one₀ hr.1 hr.2.le
    have hN : 0 ≤ f N := pow_nonneg hr.1 _
    linarith
  have htail : (K : ℝ)*(∑ n ∈ range N, (f n+f (n+1))) ≤
      (K : ℝ)+2*(K : ℝ)*(∑ n ∈ range N, f (n+1)) := by
    rw [sum_add_distrib]
    have hm := mul_le_mul_of_nonneg_left hshift (Nat.cast_nonneg (α := ℝ) K)
    nlinarith
  rw [sum_add_distrib] at htail
  change (∑ n ∈ range N, (comparisonAllocationWeight K N 0 n-comparisonBandAllocationWeight K N η n)) ≤
    (∑ n ∈ range N, if n < 2 then (1 : ℝ) else 0) +
    (∑ n ∈ range N, if (primeWinner n : ℝ) ≤ (N : ℝ)^α then (1 : ℝ) else 0) +
    (K : ℝ)*((∑ n ∈ range N, f n)+(∑ n ∈ range N, f (n+1))) at hs
  have hb : (∑ n ∈ range N, (comparisonAllocationWeight K N 0 n-comparisonBandAllocationWeight K N η n)) ≤
      2+(K : ℝ) +
      (((range N).filter fun n => (Nat.maxPrimeFac (n+1) : ℝ) ≤ (N : ℝ)^α).card : ℝ) +
      2*(K : ℝ)*(∑ n ∈ range N, f (n+1)) := by linarith
  have hd := div_le_div_of_nonneg_right hb (Nat.cast_nonneg (α := ℝ) N)
  simpa only [add_div,mul_div_assoc] using hd

/-- For every fixed positive box count, adding a sufficiently small fixed
power lower cutoff causes arbitrarily small mean loss. -/
theorem comparisonBandAllocationWeight_uniform_lower_cutoff (K : ℕ) (hK : 0 < K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, (comparisonAllocationWeight K N 0 n-comparisonBandAllocationWeight K N η n))/N < ε := by
  let α : ℝ := min (1/2) (ε/640)
  have hα : 0 < α := lt_min (by norm_num) (by positivity)
  have hα1 : α < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hαsmall : 80*α^2 ≤ ε/8 := by
    have h₁ : α ≤ 1 := hα1.le
    have h₂ : α ≤ ε/640 := min_le_right _ _
    nlinarith
  have hr := allocationAvoidanceBase_bounds K hK
  obtain ⟨η,hη,hηα,S,hS⟩ := power_prime_band_suppression α (1-1/(K : ℝ)) hα hα1 hr.1 hr.2
    (ε/(16*(K : ℝ))) (by positivity)
  have ht := tendsto_const_div_atTop_nhds_zero_nat (2+(K : ℝ))
  have hsm := smooth_power_count_eventually_le α hα.le (ε/8) (by positivity)
  refine ⟨η,hη,?_⟩
  filter_upwards [hS,ht.eventually_lt_const (show (0 : ℝ) < ε/4 by positivity),hsm,
    eventually_gt_atTop (0 : ℕ)] with N hS ht hsm hN
  obtain ⟨hpr,hmean⟩ := hS
  have hb := comparisonBandAllocationWeight_mean_loss_bound K N hK hN η α (S N) hpr
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have htail := mul_lt_mul_of_pos_left hmean (show (0 : ℝ) < 2*K by positivity)
  have he : 2*(K : ℝ)*(ε/(16*(K : ℝ))) = ε/8 := by field_simp; ring
  rw [he] at htail
  linarith

/-- Both cutoffs can be imposed, with K and eta fixed before N tends to infinity. -/
theorem comparisonBandAllocationWeight_uniform_approximation (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∃ η : ℝ, 0 < η ∧ ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ range N, (1-comparisonBandAllocationWeight K N η n))/N < ε := by
  obtain ⟨K,hK,hupper⟩ := comparisonAllocationWeight_zero_uniform_approximation (ε/2) (by positivity)
  obtain ⟨η,hη,hlower⟩ := comparisonBandAllocationWeight_uniform_lower_cutoff K hK (ε/2) (by positivity)
  refine ⟨K,hK,η,hη,?_⟩
  filter_upwards [hupper,hlower] with N hupper hlower
  have he : (∑ n ∈ range N, (1-comparisonBandAllocationWeight K N η n))/N =
      (∑ n ∈ range N, (1-comparisonAllocationWeight K N 0 n))/N +
      (∑ n ∈ range N, (comparisonAllocationWeight K N 0 n-comparisonBandAllocationWeight K N η n))/N := by
    rw [← add_div,← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro n hn
    ring
  rw [he]
  linarith

#print axioms comparisonBandAllocationWeight_mean_loss_bound
#print axioms comparisonBandAllocationWeight_uniform_lower_cutoff
#print axioms comparisonBandAllocationWeight_uniform_approximation
end Erdos371
