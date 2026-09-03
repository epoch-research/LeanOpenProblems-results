import Submission.ComparisonBandApproximation

/-! A band retention with lower cutoff greater than one excludes every empty
box. Thus a grouped weight close to one (a high probability of avoiding one
box) cannot simultaneously approximate retained comparison mass. -/
namespace Erdos371
open Finset Filter RandomBins FiniteSieve
open scoped Topology
attribute [local instance] Classical.propDecidable

namespace RandomBins

/-- Avoiding one fixed color has the exact grouped weight (1-1/K)^omega(n).
The complementary nonempty-color event contains every band allocation. -/
theorem primeAllocationBandRetention_le_nonempty_mass (K : ℕ) (hK : 0 < K)
    (Y X : ℝ) (hY : 1 < Y) (n : ℕ) :
    primeAllocationBandRetention K Y X n ≤ 1-(1-1/(K : ℝ))^n.primeFactors.card := by
  let c : Fin K := ⟨0,hK⟩
  let G := univ.filter (fun a : PrimeAtomIndex n → Fin K =>
    ∀ d, Y ≤ (boxProduct (primePowerAtom n) a d : ℝ) ∧
      (boxProduct (primePowerAtom n) a d : ℝ) ≤ X)
  let T := univ.filter (fun a : PrimeAtomIndex n → Fin K => ∀ i, a i ≠ c)
  let W := fun a : PrimeAtomIndex n → Fin K =>
    ∏ d, allocationWeight K (boxProduct (primePowerAtom n) a d)
  have hW (a : PrimeAtomIndex n → Fin K) : 0 ≤ W a := by
    apply prod_nonneg
    intro d hd
    unfold allocationWeight
    positivity
  have hdis : Disjoint G T := by
    apply disjoint_left.mpr
    intro a ha hat
    have hgood := ((mem_filter.mp ha).2 c).1
    have hav := (mem_filter.mp hat).2
    have hemp : univ.filter (fun i : PrimeAtomIndex n => a i = c) = ∅ := by
      ext i
      simp [hav i]
    have hbox : boxProduct (primePowerAtom n) a c = 1 := by
      rw [boxProduct,hemp,prod_empty]
    rw [hbox,Nat.cast_one] at hgood
    exact hY.not_ge hgood
  have htotal : (∑ a : PrimeAtomIndex n → Fin K, W a) = 1 :=
    sum_allocationWeight_boxes K hK (fun i : PrimeAtomIndex n => i.val)
      (fun i => n.factorization i.val) (primeAtom_prime n) (primeAtom_exponent_pos n)
      Subtype.val_injective
  have havoid : (∑ a ∈ T, W a) = (1-1/(K : ℝ))^n.primeFactors.card := by
    have hw (a : PrimeAtomIndex n → Fin K) : W a = ((K : ℝ)⁻¹)^Fintype.card (PrimeAtomIndex n) :=
      prod_allocationWeight_boxes K (fun i : PrimeAtomIndex n => i.val)
        (fun i => n.factorization i.val) (primeAtom_prime n) (primeAtom_exponent_pos n)
        Subtype.val_injective a
    simp_rw [hw]
    have hh := allocation_avoidance_mass K hK (univ : Finset (PrimeAtomIndex n)) c
    simpa only [T,mem_univ,forall_const,card_univ,Fintype.card_coe] using hh
  have hu : (∑ a ∈ G ∪ T, W a) ≤ 1 := by
    rw [← htotal]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun a ha hn => hW a)
  rw [sum_union hdis,havoid] at hu
  change primeAllocationBandRetention K Y X n+(1-1/(K : ℝ))^n.primeFactors.card ≤ 1 at hu
  linarith

/-- A simple upper bound valid even for n=0: nonempty-box retention cannot
exceed the expected number of atoms in one prescribed box. -/
theorem primeAllocationBandRetention_le_prime_count (K : ℕ) (hK : 0 < K)
    (Y X : ℝ) (hY : 1 < Y) (n : ℕ) :
    primeAllocationBandRetention K Y X n ≤ (n.primeFactors.card : ℝ)/K := by
  have hb := primeAllocationBandRetention_le_nonempty_mass K hK Y X hY n
  have hr := (allocationAvoidanceBase_bounds K hK).1
  have hpow := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ 1-1/(K : ℝ) by linarith)
    n.primeFactors.card
  have he : 1+(n.primeFactors.card : ℝ)*((1-1/(K : ℝ))-1) =
      1-(n.primeFactors.card : ℝ)/K := by ring
  rw [he] at hpow
  linarith

end RandomBins

lemma comparisonBandAllocationWeight_le_loser_prime_count (K N : ℕ) (hK : 0 < K)
    (η : ℝ) (hY : 1 < (N : ℝ)^η) (n : ℕ) :
    comparisonBandAllocationWeight K N η n ≤ ((losingNumber n).primeFactors.card : ℝ)/K := by
  have hl := primeAllocationBandRetention_bounds K ((N : ℝ)^η) (primeWinner n) (losingNumber n)
  have hw := (primeAllocationBandRetention_bounds K ((N : ℝ)^η) (primeWinner n)
    (winningNumber n/primeWinner n)).2.trans
      (primeAllocationRetention_mem_unit K hK _ _).2
  have hm := mul_le_of_le_one_right hl.1 hw
  exact hm.trans (primeAllocationBandRetention_le_prime_count K hK _ _ hY _)

lemma primeDivisorCountIn_all_primes (N n : ℕ) (hn : n ≠ 0) (hnN : n ≤ N) :
    primeDivisorCountIn ((N+1).primesBelow) n = n.primeFactors.card := by
  unfold primeDivisorCountIn
  congr 1
  ext p
  simp only [mem_filter,Nat.mem_primesBelow,Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hpN,hp⟩,hd⟩
    exact ⟨hp,hd,hn⟩
  · rintro ⟨hp,hd,hn⟩
    exact ⟨⟨by have := (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd).trans hnN; omega,hp⟩,hd⟩

lemma total_primeFactors_card_mean_le (N : ℕ) :
    (∑ n ∈ range N, ((n+1).primeFactors.card : ℝ)) ≤ (N : ℝ)*primeHarmonic N := by
  have he : (∑ n ∈ range N, ((n+1).primeFactors.card : ℝ)) =
      ∑ n ∈ range N, (primeDivisorCountIn ((N+1).primesBelow) (n+1) : ℝ) := by
    apply sum_congr rfl
    intro n hn
    rw [primeDivisorCountIn_all_primes N (n+1) (by omega) (mem_range.mp hn)]
  rw [he,primeDivisorCountIn_sum]
  have hp : primeReciprocalMass ((N+1).primesBelow) = primeHarmonic N := by
    rfl
  rw [← hp,primeReciprocalMass,mul_sum]
  apply sum_le_sum
  intro p hp
  have hdiv : ((N/p : ℕ) : ℝ) ≤ (N : ℝ)/p := Nat.cast_div_le
  simpa only [mul_one_div] using hdiv

/-- Uniform in the positive lower exponent: a box count large relative to the
prime harmonic sum forces small retained comparison mass. -/
theorem comparisonBandAllocationWeight_mean_prime_count_bound (K N : ℕ)
    (hK : 0 < K) (η : ℝ) (hY : 1 < (N : ℝ)^η) :
    (∑ n ∈ range N, comparisonBandAllocationWeight K N η n)/N ≤ 2*primeHarmonic N/K := by
  have hpoint (n : ℕ) : ((losingNumber n).primeFactors.card : ℝ) ≤
      (n.primeFactors.card : ℝ)+(n+1).primeFactors.card := by
    unfold losingNumber
    split_ifs
    · exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    · exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hsum := sum_le_sum (s := range N) fun n hn =>
    (comparisonBandAllocationWeight_le_loser_prime_count K N hK η hY n).trans
      (div_le_div_of_nonneg_right (hpoint n) (Nat.cast_nonneg K))
  rw [← sum_div,sum_add_distrib] at hsum
  have hshift : (∑ n ∈ range N, (n.primeFactors.card : ℝ)) ≤
      ∑ n ∈ range N, ((n+1).primeFactors.card : ℝ) := by
    have he := sum_range_succ' (fun n => (n.primeFactors.card : ℝ)) N
    rw [sum_range_succ] at he
    simp only [Nat.primeFactors_zero,card_empty,Nat.cast_zero,add_zero] at he
    have hnonneg : (0 : ℝ) ≤ N.primeFactors.card := Nat.cast_nonneg _
    linarith
  have hmean := total_primeFactors_card_mean_le N
  have hb : (∑ n ∈ range N, comparisonBandAllocationWeight K N η n) ≤
      (2*(N : ℝ)*primeHarmonic N)/K := by
    apply hsum.trans
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg K)
    linarith
  by_cases hN : N = 0
  · subst N
    simp only [range_zero,sum_empty,Nat.cast_zero,zero_div]
    unfold primeHarmonic primeReciprocalSum
    positivity
  · have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have hd := div_le_div_of_nonneg_right hb (Nat.cast_nonneg (α := ℝ) N)
    convert hd using 1
    field_simp

/-- Even a varying positive lower exponent cannot prevent loss of all mass
when K dominates the prime harmonic sum. -/
theorem largeBoxCount_varying_band_weight_tendsto_zero (K : ℕ → ℕ) (η : ℕ → ℝ)
    (hK : ∀ᶠ N : ℕ in atTop, 0 < K N) (hη : ∀ᶠ N : ℕ in atTop, 0 < η N)
    (hH : Tendsto (fun N : ℕ => primeHarmonic N/(K N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, comparisonBandAllocationWeight (K N) N (η N) n)/N) atTop (nhds 0) := by
  have ht : Tendsto (fun N : ℕ => 2*primeHarmonic N/(K N : ℝ)) atTop (nhds 0) := by
    simpa only [mul_div_assoc,mul_zero] using hH.const_mul 2
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hK,hη,eventually_gt_atTop (1 : ℕ),ht.eventually_lt_const hε] with N hK hη hN ht
  have hY : 1 < (N : ℝ)^(η N) := Real.one_lt_rpow (by exact_mod_cast hN) hη
  have hnonneg : 0 ≤ (∑ n ∈ range N, comparisonBandAllocationWeight (K N) N (η N) n)/N :=
    div_nonneg (sum_nonneg fun n hn => (comparisonBandAllocationWeight_bounds (K N) N hK (η N) n).1)
      (Nat.cast_nonneg N)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hnonneg]
  exact (comparisonBandAllocationWeight_mean_prime_count_bound (K N) N hK (η N) hY).trans_lt ht

/-- The accompanying signed limit is again only a vanishing-mass result. -/
theorem largeBoxCount_varying_band_signed_tendsto_zero (K : ℕ → ℕ) (η : ℕ → ℝ)
    (hK : ∀ᶠ N : ℕ in atTop, 0 < K N) (hη : ∀ᶠ N : ℕ in atTop, 0 < η N)
    (hH : Tendsto (fun N : ℕ => primeHarmonic N/(K N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, factorSign n*comparisonBandAllocationWeight (K N) N (η N) n)/N)
      atTop (nhds 0) := by
  have ht := largeBoxCount_varying_band_weight_tendsto_zero K η hK hη hH
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hK,ht.eventually_lt_const hε] with N hK ht
  rw [Real.dist_eq,sub_zero,abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
  apply lt_of_le_of_lt _ ht
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg (α := ℝ) N)
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro n hn
  rw [abs_mul,show |factorSign n| = 1 by simpa only [Real.norm_eq_abs] using factorSign_norm n,
    one_mul,abs_of_nonneg (comparisonBandAllocationWeight_bounds (K N) N hK (η N) n).1]

/-- Consequently the mean approximation loss tends to one, uniformly over
all choices of positive moving lower exponents under the size hypothesis. -/
theorem largeBoxCount_varying_band_mean_loss_tendsto_one (K : ℕ → ℕ) (η : ℕ → ℝ)
    (hK : ∀ᶠ N : ℕ in atTop, 0 < K N) (hη : ∀ᶠ N : ℕ in atTop, 0 < η N)
    (hH : Tendsto (fun N : ℕ => primeHarmonic N/(K N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ range N, (1-comparisonBandAllocationWeight (K N) N (η N) n))/N)
      atTop (nhds 1) := by
  have ht := (largeBoxCount_varying_band_weight_tendsto_zero K η hK hη hH).const_sub 1
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,mul_one,sub_div,
    div_self (by exact_mod_cast hN.ne')]

#print axioms primeAllocationBandRetention_le_nonempty_mass
#print axioms comparisonBandAllocationWeight_mean_prime_count_bound
#print axioms largeBoxCount_varying_band_signed_tendsto_zero
#print axioms largeBoxCount_varying_band_mean_loss_tendsto_one
end Erdos371
