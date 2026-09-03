import Submission.No9PrimeEmbedding

/-! Intermediate necessary condition only: an odd cover must use a multiple of 9.
This does not settle the unrestricted odd covering problem. -/
namespace Erdos7No9Certificate
open scoped BigOperators
open Erdos7Reduction
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

lemma factorization_three_le_one (m : ℕ) (hm : m≠0) (h9 : ¬9 ∣ m) : m.factorization 3 ≤ 1 := by
  by_contra hh
  have he : 2 ≤ m.factorization 3 := by omega
  have hd := (show Nat.Prime 3 by norm_num).pow_dvd_iff_le_factorization (k:=2) hm
  have hp : 3^2 ∣ m := hd.mpr he
  exact h9 (by simpa only [show (3:ℕ)^2=9 by norm_num] using hp)

theorem arithmetic_exists_nine {κ : Type*} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a) : ∃ k,9 ∣ m k := by
  classical
  by_contra! hno
  have hm0 (k : κ) : m k≠0 := by have := (hc.2.1 k).1; omega
  let P := Finset.univ.biUnion (fun k => (m k).primeFactors)
  have hP (q : ℕ) (hq : q∈P) : q.Prime ∧ 3 ≤ q := by
    obtain ⟨k,hk,hqk⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hprime,hdvd,hzero⟩ := Nat.mem_primeFactors.mp hqk
    have h2 : q≠2 := by
      intro heq
      rw [heq] at hdvd
      exact (Nat.not_even_iff_odd.mpr (hc.2.1 k).2) (even_iff_two_dvd.mpr hdvd)
    exact ⟨hprime,by have := hprime.two_le; omega⟩
  let T := P.filter (fun q => 1500000 < q)
  have hT (q : ℕ) (hq : q∈T) : q.Prime ∧ 1500000 < q :=
    ⟨(hP q (Finset.mem_filter.mp hq).1).1,(Finset.mem_filter.mp hq).2⟩
  let p := extendedCandidate T
  let e (k : κ) (i : Fin (smallLength+T.card)) := (m k).factorization (p i)
  let E := paddedExponent p e
  have hsched : PrimeSchedule p E := padded_prime_schedule T hT e
  have hpinj : Function.Injective p := hsched.monotone.injective
  have hprod (k : κ) : m k=∏ i,p i^e k i := by
    let Q := Finset.univ.image p
    have hsub : (m k).primeFactors ⊆ Q := by
      intro q hq
      have hqP : q∈P := Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,hq⟩
      have hqprime := hP q hqP
      obtain ⟨i,hi⟩ := extendedCandidate_covers T q hqprime.1 hqprime.2 (fun h => Finset.mem_filter.mpr ⟨hqP,h⟩)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
    have hh := Erdos7Compression.factorization_product_over_superset (m k) (hm0 k) Q hsub
    rw [Finset.prod_coe_sort Q (fun q => q^(m k).factorization q)] at hh
    rw [hh]
    exact Finset.prod_image (fun i _ j _ hij => hpinj hij)
  have hei : Function.Injective e := by
    intro k l hkl
    apply hc.1
    rw [hprod k,hprod l,hkl]
  have he0 (k : κ) : ∃ i,e k i≠0 := by
    by_contra! hz
    have hh := (hc.2.1 k).1
    rw [hprod k] at hh
    simp only [hz,pow_zero,Finset.prod_const_one] at hh
    omega
  have he3 (k : κ) (i : Fin (smallLength+T.card)) (hi : p i=3) : e k i ≤ 1 := by
    dsimp only [e]
    rw [hi]
    exact factorization_three_le_one (m k) (hm0 k) (hno k)
  have heE : ∀ k i,e k i ≤ E i := paddedExponent_le p e he3
  let S := Finset.univ.filter (fun i : Fin (smallLength+T.card) => (p i).Prime)
  have heS (k : κ) (i : Fin (smallLength+T.card)) (hi : e k i≠0) : i∈S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    by_contra hn
    exact hi (Nat.factorization_eq_zero_of_non_prime (m k) hn)
  have hcop : (S : Set (Fin (smallLength+T.card))).Pairwise (Function.onFun Nat.Coprime p) := by
    intro i hi j hj hij
    have hpi : (p i).Prime := (Finset.mem_filter.mp (show i∈S from hi)).2
    have hpj : (p j).Prime := (Finset.mem_filter.mp (show j∈S from hj)).2
    exact (Nat.coprime_primes hpi hpj).mpr (fun hh => hij (hpinj hh))
  apply scheduled_arithmetic_not_cover p E hsched S hcop e hei he0 heE heS a
  simpa only [← hprod] using hc.2.2

theorem exists_nine (C : StrictCoveringSystem ℤ) (hodd : ∀ i,¬C.moduli i ≤ Ideal.span {2}) :
    ∃ i,9 ∣ (C.moduli i).absNorm := by
  letI := C.fintypeIndex
  exact arithmetic_exists_nine (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C,fun i => ⟨moduli_absNorm_gt_one C i,(ideal_not_le_two_iff _).mp (hodd i)⟩,arithmetic_cover C⟩

#print axioms arithmetic_exists_nine
#print axioms exists_nine
end Erdos7No9Certificate
