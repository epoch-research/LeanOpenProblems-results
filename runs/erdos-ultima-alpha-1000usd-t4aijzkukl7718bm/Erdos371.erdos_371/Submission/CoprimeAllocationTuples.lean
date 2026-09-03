import Submission.PrimeAllocationRetention

/-! Prime-power allocations are exactly positive pairwise-coprime factor tuples.
This is an exact change of variables, not an estimate for shifted sums. -/
namespace Erdos371.RandomBins
open Finset

/-- Ordered factor tuples with each prime supported in just one coordinate. -/
def CoprimeFactorTuple (K n : ℕ) (b : Fin K → ℕ) : Prop :=
  (∀ c, 0 < b c) ∧ Pairwise (fun c d => (b c).Coprime (b d)) ∧ ∏ c, b c = n

lemma primeBoxProducts_pairwise_coprime (K n : ℕ) (a : PrimeAtomIndex n → Fin K) :
    Pairwise (fun c d => (boxProduct (primePowerAtom n) a c).Coprime
      (boxProduct (primePowerAtom n) a d)) := by
  classical
  intro c d hcd
  by_contra h
  obtain ⟨p,hp,hpc,hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hcp : p ∈ (boxProduct (primePowerAtom n) a c).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp,hpc,(boxProduct_pos _ (primePowerAtom_pos n) _ _).ne'⟩
  have hdp : p ∈ (boxProduct (primePowerAtom n) a d).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp,hpd,(boxProduct_pos _ (primePowerAtom_pos n) _ _).ne'⟩
  unfold primePowerAtom at hcp hdp
  rw [primeFactors_boxProduct K (fun i : PrimeAtomIndex n => i.val)
    (fun i => n.factorization i.val) (primeAtom_prime n) (primeAtom_exponent_pos n)] at hcp hdp
  obtain ⟨i,hi,hip⟩ := mem_image.mp hcp
  obtain ⟨j,hj,hjp⟩ := mem_image.mp hdp
  have hij : i = j := Subtype.ext (hip.trans hjp.symm)
  subst j
  exact hcd ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2)

lemma primeBoxProducts_coprimeFactorTuple (K n : ℕ) (hn : n ≠ 0)
    (a : PrimeAtomIndex n → Fin K) :
    CoprimeFactorTuple K n (boxProduct (primePowerAtom n) a) := by
  refine ⟨boxProduct_pos _ (primePowerAtom_pos n) a,
    primeBoxProducts_pairwise_coprime K n a,?_⟩
  rw [prod_boxProduct,prod_primePowerAtom n hn]

/-- In a coprime tuple, a prime dividing the product has a unique coordinate. -/
lemma CoprimeFactorTuple.existsUnique_prime_divisor {K n : ℕ} {b : Fin K → ℕ}
    (hb : CoprimeFactorTuple K n b) (p : ℕ) (hp : p.Prime) (hd : p ∣ n) :
    ∃! c, p ∣ b c := by
  rw [← hb.2.2] at hd
  obtain ⟨c,hc,hpc⟩ := (hp.prime.dvd_finset_prod_iff b).mp hd
  refine ⟨c,hpc,?_⟩
  intro d hpd
  by_contra hdc
  have hg := Nat.dvd_gcd hpd hpc
  rw [hb.2.1 hdc] at hg
  exact hp.not_dvd_one hg

lemma CoprimeFactorTuple.factorization_eq_of_dvd {K n : ℕ} {b : Fin K → ℕ}
    (hb : CoprimeFactorTuple K n b) (p : ℕ) (hp : p.Prime) (c : Fin K)
    (hpc : p ∣ b c) : (b c).factorization p = n.factorization p := by
  rw [← hb.2.2,Nat.factorization_prod_apply (fun d _ => (hb.1 d).ne')]
  symm
  apply sum_eq_single c
  · intro d hd hdc
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hpd
    exact hp.not_dvd_one (by simpa only [hb.2.1 hdc] using Nat.dvd_gcd hpd hpc)
  · simp

/-- Surjectivity onto all positive coprime ordered factorizations. -/
theorem exists_primeAllocation_of_coprimeFactorTuple (K n : ℕ) (hn : n ≠ 0)
    (b : Fin K → ℕ) (hb : CoprimeFactorTuple K n b) :
    ∃ a : PrimeAtomIndex n → Fin K, boxProduct (primePowerAtom n) a = b := by
  classical
  have he (i : PrimeAtomIndex n) : ∃! c, i.val ∣ b c :=
    hb.existsUnique_prime_divisor i.val (primeAtom_prime n i)
      (Nat.mem_primeFactors.mp i.property).2.1
  let a : PrimeAtomIndex n → Fin K := fun i => (he i).exists.choose
  have ha (i : PrimeAtomIndex n) (c : Fin K) : a i = c ↔ i.val ∣ b c := by
    have hac : i.val ∣ b (a i) := (he i).exists.choose_spec
    constructor
    · intro h; simpa only [h] using hac
    · intro h; exact (ExistsUnique.unique (he i) hac h)
  refine ⟨a,?_⟩
  funext c
  rw [boxProduct]
  calc
    (∏ i ∈ univ.filter (fun i : PrimeAtomIndex n => a i = c), primePowerAtom n i) =
        ∏ p ∈ (b c).primeFactors, p^(b c).factorization p := by
      apply prod_bij (fun i _ => i.val)
      · intro i hi
        exact Nat.mem_primeFactors.mpr ⟨primeAtom_prime n i,
          (ha i c).mp (mem_filter.mp hi).2,(hb.1 c).ne'⟩
      · intro i hi j hj h
        exact Subtype.ext h
      · intro p hp
        have hd : b c ∣ n := by rw [← hb.2.2]; exact dvd_prod_of_mem b (mem_univ c)
        have hpn : p ∈ n.primeFactors := Nat.primeFactors_mono hd hn hp
        refine ⟨⟨p,hpn⟩,mem_filter.mpr ⟨mem_univ _,?_⟩,rfl⟩
        exact (ha ⟨p,hpn⟩ c).mpr (Nat.mem_primeFactors.mp hp).2.1
      · intro i hi
        unfold primePowerAtom
        rw [← hb.factorization_eq_of_dvd i.val (primeAtom_prime n i) c
          ((ha i c).mp (mem_filter.mp hi).2)]
    _ = b c := Nat.factorization_prod_pow_eq_self (hb.1 c).ne'

/-- A common finite ambient box for tuple sums. -/
noncomputable def smallCoprimeTuples (K M : ℕ) (X : ℝ) : Finset (Fin K → ℕ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin K => Icc 1 M)).filter fun b =>
    Pairwise (fun c d => (b c).Coprime (b d)) ∧ ∀ c, (b c : ℝ) ≤ X

lemma mem_smallCoprimeTuples (K M : ℕ) (X : ℝ) (b : Fin K → ℕ) :
    b ∈ smallCoprimeTuples K M X ↔
      (∀ c, 0 < b c ∧ b c ≤ M) ∧
      Pairwise (fun c d => (b c).Coprime (b d)) ∧ ∀ c, (b c : ℝ) ≤ X := by
  classical
  simp only [smallCoprimeTuples,mem_filter,Fintype.mem_piFinset,mem_Icc]
  rfl

lemma CoprimeFactorTuple.coord_le {K n : ℕ} {b : Fin K → ℕ}
    (hb : CoprimeFactorTuple K n b) (c : Fin K) : b c ≤ n := by
  rw [← hb.2.2]
  exact single_le_prod' (fun d _ => hb.1 d) (mem_univ c)

/-- Exact transport of retention to a sum over pairwise-coprime integer tuples.
The weight is the product of one-coordinate weights. -/
theorem primeAllocationRetention_eq_tuple_sum (K M n : ℕ) (hn : n ≠ 0)
    (hnM : n ≤ M) (X : ℝ) :
    primeAllocationRetention K X n =
      ∑ b ∈ (smallCoprimeTuples K M X).filter (fun b => ∏ c, b c = n),
        ∏ c, allocationWeight K (b c) := by
  classical
  unfold primeAllocationRetention
  apply sum_bij (fun a _ => boxProduct (primePowerAtom n) a)
  · intro a ha
    have hat := primeBoxProducts_coprimeFactorTuple K n hn a
    apply mem_filter.mpr
    refine ⟨(mem_smallCoprimeTuples _ _ _ _).mpr ⟨?_,hat.2.1,?_⟩,hat.2.2⟩
    · exact fun c => ⟨hat.1 c,(hat.coord_le c).trans hnM⟩
    · exact (mem_filter.mp ha).2
  · intro a ha a' ha' heq
    exact boxProducts_injective K (fun i : PrimeAtomIndex n => i.val)
      (fun i => n.factorization i.val) (primeAtom_prime n) (primeAtom_exponent_pos n)
      Subtype.val_injective heq
  · intro b hb
    obtain ⟨hb,hprod⟩ := mem_filter.mp hb
    obtain ⟨hpos,hcop,hsize⟩ := (mem_smallCoprimeTuples _ _ _ _).mp hb
    obtain ⟨a,ha⟩ := exists_primeAllocation_of_coprimeFactorTuple K n hn b
      ⟨fun c => (hpos c).1,hcop,hprod⟩
    refine ⟨a,mem_filter.mpr ⟨mem_univ _,?_⟩,ha⟩
    simpa only [ha] using hsize
  · intro a ha; rfl

#print axioms exists_primeAllocation_of_coprimeFactorTuple
#print axioms primeAllocationRetention_eq_tuple_sum
end Erdos371.RandomBins
