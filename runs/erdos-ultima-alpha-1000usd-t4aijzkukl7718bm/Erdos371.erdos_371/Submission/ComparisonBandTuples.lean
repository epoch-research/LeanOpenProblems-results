import Submission.ComparisonBandApproximation
import Submission.ComparisonTupleExpansion

/-! Exact transport to power-sized coprime factor tuples, followed by an
explicitly conditional signed-cancellation criterion. -/
namespace Erdos371
open Finset Filter RandomBins
open scoped Topology
attribute [local instance] Classical.propDecidable

namespace RandomBins

noncomputable def bandCoprimeTuples (K M : ℕ) (Y X : ℝ) : Finset (Fin K → ℕ) :=
  (smallCoprimeTuples K M X).filter fun b => ∀ c, Y ≤ (b c : ℝ)

lemma mem_bandCoprimeTuples (K M : ℕ) (Y X : ℝ) (b : Fin K → ℕ) :
    b ∈ bandCoprimeTuples K M Y X ↔
      (∀ c, 0 < b c ∧ b c ≤ M) ∧
      Pairwise (fun c d => (b c).Coprime (b d)) ∧
      (∀ c, (b c : ℝ) ≤ X) ∧ ∀ c, Y ≤ (b c : ℝ) := by
  simp only [bandCoprimeTuples,mem_filter,mem_smallCoprimeTuples,and_assoc]

/-- The band retention is a separable sum over a common finite tuple box. -/
theorem primeAllocationBandRetention_eq_tuple_sum (K M n : ℕ) (hn : n ≠ 0)
    (hnM : n ≤ M) (Y X : ℝ) :
    primeAllocationBandRetention K Y X n =
      ∑ b ∈ (bandCoprimeTuples K M Y X).filter (fun b => ∏ c, b c = n),
        ∏ c, allocationWeight K (b c) := by
  unfold primeAllocationBandRetention
  apply sum_bij (fun a _ => boxProduct (primePowerAtom n) a)
  · intro a ha
    have hat := primeBoxProducts_coprimeFactorTuple K n hn a
    apply mem_filter.mpr
    refine ⟨(mem_bandCoprimeTuples _ _ _ _ _).mpr ⟨?_,hat.2.1,?_,?_⟩,hat.2.2⟩
    · exact fun c => ⟨hat.1 c,(hat.coord_le c).trans hnM⟩
    · exact fun c => ((mem_filter.mp ha).2 c).2
    · exact fun c => ((mem_filter.mp ha).2 c).1
  · intro a ha a' ha' heq
    exact boxProducts_injective K (fun i : PrimeAtomIndex n => i.val)
      (fun i => n.factorization i.val) (primeAtom_prime n) (primeAtom_exponent_pos n)
      Subtype.val_injective heq
  · intro b hb
    obtain ⟨hb,hprod⟩ := mem_filter.mp hb
    obtain ⟨hpos,hcop,hupper,hlower⟩ := (mem_bandCoprimeTuples _ _ _ _ _).mp hb
    obtain ⟨a,ha⟩ := exists_primeAllocation_of_coprimeFactorTuple K n hn b
      ⟨fun c => (hpos c).1,hcop,hprod⟩
    refine ⟨a,mem_filter.mpr ⟨mem_univ _,?_⟩,ha⟩
    simpa only [ha] using fun c => And.intro (hlower c) (hupper c)
  · intro a ha
    rfl

end RandomBins

/-- Both product equations, the lower power cutoff, and the exact winning-prime
upper cutoff remain present in the tuple representation. -/
theorem comparisonBandAllocationWeight_eq_tuple_sum (K N n : ℕ) (η : ℝ)
    (hn : 1 < n) (hnN : n < N) :
    comparisonBandAllocationWeight K N η n =
      ∑ A ∈ (bandCoprimeTuples K N ((N : ℝ)^η) (primeWinner n)).filter
        (fun A => ∏ c, A c = losingNumber n),
      ∑ B ∈ (bandCoprimeTuples K N ((N : ℝ)^η) (primeWinner n)).filter
        (fun B => primeWinner n * ∏ c, B c = winningNumber n),
        (∏ c, allocationWeight K (A c)) * (∏ c, allocationWeight K (B c)) := by
  obtain ⟨hl,hw,hlN,hwN⟩ := comparison_numbers_bounds n hn
  obtain ⟨hp,hlp,hwp⟩ := comparison_numbers_prime_factors n hn
  have hd : primeWinner n ∣ winningNumber n := by
    rw [← hwp]
    exact Nat.maxPrimeFac_dvd
  have hq : 0 < winningNumber n / primeWinner n :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
  have heq : ∀ q : ℕ, q = winningNumber n / primeWinner n ↔ primeWinner n*q = winningNumber n := by
    intro q
    constructor
    · rintro rfl
      exact Nat.mul_div_cancel' hd
    · intro h
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      rw [Nat.mul_div_cancel' hd]
      exact h
  unfold comparisonBandAllocationWeight
  rw [primeAllocationBandRetention_eq_tuple_sum K N (losingNumber n) (by omega) (by omega),
    primeAllocationBandRetention_eq_tuple_sum K N (winningNumber n / primeWinner n) hq.ne'
      ((Nat.div_le_self _ _).trans (by omega)),sum_mul_sum]
  simp_rw [heq]

lemma comparisonBandAllocationWeight_signed_error_bound (K N : ℕ) (hK : 0 < K) (η : ℝ) :
    |(∑ n ∈ range N, factorSign n)/N -
      (∑ n ∈ range N, factorSign n*comparisonBandAllocationWeight K N η n)/N| ≤
        (∑ n ∈ range N, (1-comparisonBandAllocationWeight K N η n))/N := by
  rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg (α := ℝ) N)
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro n hn
  have hW := (comparisonBandAllocationWeight_bounds K N hK η n).2.trans
    (comparisonAllocationWeight_mem_unit K N hK 0 n).2
  have hsign : |factorSign n| = 1 := by simpa only [Real.norm_eq_abs] using factorSign_norm n
  rw [show factorSign n-factorSign n*comparisonBandAllocationWeight K N η n =
      factorSign n*(1-comparisonBandAllocationWeight K N η n) by ring,
    abs_mul,hsign,one_mul,abs_of_nonneg (sub_nonneg.mpr hW)]

/-- A sufficient signed criterion on power-sized factor tuples. The hypothesis
is the missing arithmetic cancellation estimate, not a conclusion of this file. -/
theorem density_of_bandAllocation_cancellation
    (hcancel : ∀ K : ℕ, 0 < K → ∀ η : ℝ, 0 < η → Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, factorSign n*comparisonBandAllocationWeight K N η n)/N) atTop (nhds 0)) :
    {n | Nat.maxPrimeFac (n+1) > Nat.maxPrimeFac n}.HasDensity (1/2) := by
  rw [density_iff_signed_count]
  simp_rw [← factorSign_sum_eq_count_difference]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K,hK,η,hη,ha⟩ := comparisonBandAllocationWeight_uniform_approximation (ε/2) (by positivity)
  have hc := Metric.tendsto_nhds.mp (hcancel K hK η hη) (ε/2) (by positivity)
  filter_upwards [ha,hc] with N ha hc
  rw [Real.dist_eq,sub_zero] at hc ⊢
  have hb := comparisonBandAllocationWeight_signed_error_bound K N hK η
  have ht := abs_sub_le ((∑ n ∈ range N, factorSign n)/N)
    ((∑ n ∈ range N, factorSign n*comparisonBandAllocationWeight K N η n)/N) 0
  simp only [sub_zero] at ht
  linarith

#print axioms comparisonBandAllocationWeight_eq_tuple_sum
#print axioms density_of_bandAllocation_cancellation
end Erdos371
