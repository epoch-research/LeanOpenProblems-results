import Submission.RandomFactorProducts

/-! A multiplicatively separable weight for assigning distinct prime-power
atoms to boxes. It normalizes all assignments, not only the retained ones. -/
namespace Erdos371.RandomBins
open Finset

section PrimePowers
variable {ι : Type*} [DecidableEq ι]

lemma primeFactors_prod_prime_powers (p e : ι → ℕ) (S : Finset ι)
    (hp : ∀ i, (p i).Prime) (he : ∀ i, 0 < e i) :
    (∏ i ∈ S, (p i)^(e i)).primeFactors = S.image p := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hpos : 0 < ∏ j ∈ S, (p j)^(e j) := prod_pos (fun j hj => Nat.pow_pos (hp j).pos)
    rw [prod_insert hi,Nat.primeFactors_mul (Nat.pow_pos (hp i).pos).ne' hpos.ne',
      Nat.primeFactors_pow (p i) (he i).ne',(hp i).primeFactors,ih,
      singleton_union,image_insert]

variable [Fintype ι]

lemma primeFactors_boxProduct (K : ℕ) (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (he : ∀ i, 0 < e i) (a : ι → Fin K) (c : Fin K) :
    (boxProduct (fun i => (p i)^(e i)) a c).primeFactors =
      (univ.filter (fun i => a i = c)).image p :=
  primeFactors_prod_prime_powers p e _ hp he

lemma boxProducts_injective (K : ℕ) (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (he : ∀ i, 0 < e i) (hinj : Function.Injective p) :
    Function.Injective (fun a : ι → Fin K => boxProduct (fun i => (p i)^(e i)) a) := by
  intro a b hab
  funext i
  have hmem : p i ∈ (boxProduct (fun i => (p i)^(e i)) a (a i)).primeFactors := by
    rw [primeFactors_boxProduct K p e hp he]
    exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,rfl⟩,rfl⟩
  have heq := congrFun hab (a i)
  dsimp only at heq
  rw [heq,primeFactors_boxProduct K p e hp he] at hmem
  obtain ⟨j,hj,hji⟩ := mem_image.mp hmem
  have hji' : j = i := hinj hji
  subst j
  exact (mem_filter.mp hj).2.symm

lemma sum_box_primeFactors_card (K : ℕ) (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (he : ∀ i, 0 < e i) (hinj : Function.Injective p)
    (a : ι → Fin K) :
    (∑ c : Fin K, (boxProduct (fun i => (p i)^(e i)) a c).primeFactors.card) =
      Fintype.card ι := by
  simp_rw [primeFactors_boxProduct K p e hp he,
    card_image_of_injective _ hinj]
  have h := sum_card_fiberwise_eq_card_filter (univ : Finset ι) (univ : Finset (Fin K)) a
  simpa only [mem_univ,filter_true,card_univ] using h

noncomputable def allocationWeight (K n : ℕ) : ℝ := ((K : ℝ)⁻¹)^n.primeFactors.card

/-- The product of the weights of all boxes is independent of their
allocation. The prime powers are assigned whole and have distinct primes. -/
lemma prod_allocationWeight_boxes (K : ℕ) (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (he : ∀ i, 0 < e i) (hinj : Function.Injective p)
    (a : ι → Fin K) :
    (∏ c : Fin K, allocationWeight K (boxProduct (fun i => (p i)^(e i)) a c)) =
      ((K : ℝ)⁻¹)^Fintype.card ι := by
  unfold allocationWeight
  rw [prod_pow_eq_pow_sum,sum_box_primeFactors_card K p e hp he hinj]

/-- The total mass of all allocations is exactly one. -/
theorem sum_allocationWeight_boxes (K : ℕ) (hK : 0 < K) (p e : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (he : ∀ i, 0 < e i) (hinj : Function.Injective p) :
    (∑ a : ι → Fin K, ∏ c : Fin K,
      allocationWeight K (boxProduct (fun i => (p i)^(e i)) a c)) = 1 := by
  simp_rw [prod_allocationWeight_boxes K p e hp he hinj]
  simp only [sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,inv_pow]
  apply mul_inv_cancel₀
  exact pow_ne_zero _ (by exact_mod_cast hK.ne')

/-- Restricting to small boxes costs at most the collision bound, while the
weight remains a product of one-variable multiplicative factors. -/
theorem good_prime_power_allocation_weight_lower (K N : ℕ) (hK : 0 < K) (hN : 1 < N)
    (p e : ι → ℕ) (hp : ∀ i, (p i).Prime) (he : ∀ i, 0 < e i)
    (hinj : Function.Injective p) (hprod : (∏ i : ι, (p i)^(e i)) ≤ N)
    (u δ : ℝ) (hu : 0 < u) (hδ : 0 < δ)
    (hmax : ∀ i, ((p i)^(e i) : ℝ) ≤ (N : ℝ)^(u-δ)) :
    1 - 1/((K : ℝ)*u*δ) ≤
      ∑ a ∈ univ.filter (fun a : ι → Fin K =>
        ∀ c, (boxProduct (fun i => (p i)^(e i)) a c : ℝ) ≤ (N : ℝ)^u),
        ∏ c : Fin K, allocationWeight K (boxProduct (fun i => (p i)^(e i)) a c) := by
  classical
  simp_rw [prod_allocationWeight_boxes K p e hp he hinj]
  simp only [sum_const,nsmul_eq_mul,inv_pow]
  rw [← div_eq_mul_inv]
  exact product_good_fraction_lower K N hK hN (fun i => (p i)^(e i))
    (fun i => Nat.pow_pos (hp i).pos) hprod u δ hu hδ (by simpa only [Nat.cast_pow] using hmax)

/-- On coprime arguments, allocationWeight is multiplicative. This does not
assert any cancellation for adjacent or shifted products of these weights. -/
lemma allocationWeight_mul_of_coprime (K a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a.Coprime b) :
    allocationWeight K (a*b) = allocationWeight K a * allocationWeight K b := by
  unfold allocationWeight
  rw [Nat.primeFactors_mul ha hb,card_union_of_disjoint,pow_add]
  apply disjoint_left.mpr
  intro q hqa hqb
  obtain ⟨hq,hqa,ha⟩ := Nat.mem_primeFactors.mp hqa
  have hqb := (Nat.mem_primeFactors.mp hqb).2.1
  exact hq.not_dvd_one (by simpa only [hab] using Nat.dvd_gcd hqa hqb)

#print axioms boxProducts_injective
#print axioms prod_allocationWeight_boxes
#print axioms sum_allocationWeight_boxes
#print axioms good_prime_power_allocation_weight_lower
#print axioms allocationWeight_mul_of_coprime
end PrimePowers
end Erdos371.RandomBins
