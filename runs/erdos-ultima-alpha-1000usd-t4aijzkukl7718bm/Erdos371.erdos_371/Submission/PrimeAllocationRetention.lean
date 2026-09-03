import Submission.PrimePowerAllocationWeights
import Submission.PrimePowerOvershoot

/-! Retention weights for actual prime-power allocations. They are normalized
by the number of all assignments, with a product of one-variable weights. -/
namespace Erdos371
open Finset
namespace RandomBins

abbrev PrimeAtomIndex (n : ℕ) := {p : ℕ // p ∈ n.primeFactors}

def primePowerAtom (n : ℕ) (i : PrimeAtomIndex n) : ℕ := i.val ^ n.factorization i.val

lemma primeAtom_prime (n : ℕ) (i : PrimeAtomIndex n) : i.val.Prime :=
  (Nat.mem_primeFactors.mp i.property).1

lemma primeAtom_exponent_pos (n : ℕ) (i : PrimeAtomIndex n) : 0 < n.factorization i.val := by
  obtain ⟨hp,hd,hn⟩ := Nat.mem_primeFactors.mp i.property
  exact hp.factorization_pos_of_dvd hn hd

lemma primePowerAtom_pos (n : ℕ) (i : PrimeAtomIndex n) : 0 < primePowerAtom n i :=
  Nat.pow_pos (primeAtom_prime n i).pos

lemma prod_primePowerAtom (n : ℕ) (hn : n ≠ 0) : (∏ i : PrimeAtomIndex n, primePowerAtom n i) = n := by
  rw [univ_eq_attach]
  change (∏ i ∈ n.primeFactors.attach, i.val ^ n.factorization i.val) = n
  rw [prod_attach n.primeFactors (fun p => p ^ n.factorization p)]
  exact Nat.factorization_prod_pow_eq_self hn

noncomputable def primeAllocationRetention (K : ℕ) (X : ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑ a ∈ univ.filter (fun a : PrimeAtomIndex n → Fin K =>
      ∀ c, (boxProduct (primePowerAtom n) a c : ℝ) ≤ X),
    ∏ c : Fin K, allocationWeight K (boxProduct (primePowerAtom n) a c)

lemma primeAllocationRetention_mem_unit (K : ℕ) (hK : 0 < K) (X : ℝ) (n : ℕ) :
    0 ≤ primeAllocationRetention K X n ∧ primeAllocationRetention K X n ≤ 1 := by
  classical
  have hnonneg (a : PrimeAtomIndex n → Fin K) :
      0 ≤ ∏ c : Fin K, allocationWeight K (boxProduct (primePowerAtom n) a c) := by
    apply prod_nonneg
    intro c hc
    unfold allocationWeight
    positivity
  constructor
  · exact sum_nonneg (fun a ha => hnonneg a)
  · have htot : (∑ a : PrimeAtomIndex n → Fin K, ∏ c : Fin K,
        allocationWeight K (boxProduct (primePowerAtom n) a c)) = 1 :=
      sum_allocationWeight_boxes K hK (fun i : PrimeAtomIndex n => i.val)
        (fun i => n.factorization i.val) (primeAtom_prime n) (primeAtom_exponent_pos n)
        Subtype.val_injective
    rw [← htot]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun a ha hnot => hnonneg a)

lemma primeAllocationRetention_lower (K N n : ℕ) (hK : 0 < K) (hN : 1 < N)
    (hn : 0 < n) (hnN : n ≤ N) (u δ : ℝ) (hu : 0 < u) (hδ : 0 < δ)
    (hatom : ∀ i : PrimeAtomIndex n, (primePowerAtom n i : ℝ) ≤ (N : ℝ)^(u-δ)) :
    1 - 1/((K : ℝ)*u*δ) ≤ primeAllocationRetention K ((N : ℝ)^u) n := by
  apply good_prime_power_allocation_weight_lower K N hK hN
    (fun i : PrimeAtomIndex n => i.val) (fun i => n.factorization i.val)
    (primeAtom_prime n) (primeAtom_exponent_pos n) Subtype.val_injective
  · change (∏ i : PrimeAtomIndex n, primePowerAtom n i) ≤ N
    rw [prod_primePowerAtom n hn.ne']
    exact hnN
  · exact hu
  · exact hδ
  · simpa only [primePowerAtom,Nat.cast_pow] using hatom

lemma rpow_log_quotient (N p : ℕ) (hN : 1 < N) (hp : 0 < p) :
    (N : ℝ)^(Real.log p / Real.log N) = p := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [Real.rpow_def_of_pos hNr]
  have he : Real.log N * (Real.log p/Real.log N) = Real.log p := by field_simp
  rw [he,Real.exp_log (by exact_mod_cast hp)]

/-- A small power inflation provides a uniform logarithmic buffer around
all atoms bounded by p. The lower bound p>=N^v keeps the error uniform. -/
theorem primeAllocationRetention_inflated_bound (K N n p : ℕ)
    (hK : 0 < K) (hN : 1 < N) (hn : 0 < n) (hnN : n ≤ N) (hp : 0 < p)
    (v δ : ℝ) (hv : 0 < v) (hδ : 0 < δ) (hpN : (N : ℝ)^v ≤ p)
    (hatom : ∀ i : PrimeAtomIndex n, primePowerAtom n i ≤ p) :
    1 - primeAllocationRetention K ((p : ℝ)*(N : ℝ)^δ) n ≤ 1/((K : ℝ)*v*δ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hvp : v ≤ Real.log p/Real.log N := by
    apply (le_div_iff₀ hlog).mpr
    have h := Real.log_le_log (Real.rpow_pos_of_pos hNr v) hpN
    rwa [Real.log_rpow hNr] at h
  let u : ℝ := Real.log p/Real.log N + δ
  have hu : 0 < u := by dsimp [u]; linarith
  have hexp : (N : ℝ)^u = (p : ℝ)*(N : ℝ)^δ := by
    rw [show u = Real.log p/Real.log N+δ from rfl,Real.rpow_add hNr,rpow_log_quotient N p hN hp]
  have hsmall : ∀ i : PrimeAtomIndex n, (primePowerAtom n i : ℝ) ≤ (N : ℝ)^(u-δ) := by
    intro i
    rw [show u-δ = Real.log p/Real.log N by dsimp [u]; ring,rpow_log_quotient N p hN hp]
    exact_mod_cast hatom i
  have hret := primeAllocationRetention_lower K N n hK hN hn hnN u δ hu hδ hsmall
  rw [hexp] at hret
  have hden : (K : ℝ)*v*δ ≤ (K : ℝ)*u*δ := by
    apply mul_le_mul_of_nonneg_right _ hδ.le
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    dsimp [u]
    linarith
  have hdiv : 1/((K : ℝ)*u*δ) ≤ 1/((K : ℝ)*v*δ) :=
    one_div_le_one_div_of_le (by positivity) hden
  linarith

/-- A divisor inherits the atom bound of an integer with no prime-power
overshoot; this applies to the winning cofactor as well as to the loser. -/
lemma divisor_primePowerAtom_le (d n p : ℕ) (hd : 0 < d) (hn : 0 < n)
    (hdn : d ∣ n) (hno : ¬primePowerOvershoot n) (hp : Nat.maxPrimeFac n ≤ p)
    (i : PrimeAtomIndex d) : primePowerAtom d i ≤ p := by
  have himem : i.val ∈ n.primeFactors := Nat.primeFactors_mono hdn hn.ne' i.property
  have hbound : i.val^n.factorization i.val ≤ Nat.maxPrimeFac n := by
    by_contra h
    exact hno ⟨i.val,himem,by omega⟩
  have he : d.factorization i.val ≤ n.factorization i.val :=
    (Nat.factorization_le_iff_dvd hd.ne' hn.ne').mpr hdn i.val
  exact (Nat.pow_le_pow_right (primeAtom_prime d i).pos he).trans (hbound.trans hp)

#print axioms primeAllocationRetention_mem_unit
#print axioms primeAllocationRetention_inflated_bound
#print axioms divisor_primePowerAtom_le
end RandomBins
end Erdos371
