import Submission.NinetyThreeModuli
import Submission.Forest93Shapes

/-! Equality in the digit-weight lower bound determines the93-class profile. -/
namespace Erdos7Forest93Profile
open scoped BigOperators
open Erdos7Reduction Erdos7Digits Erdos7Compression Erdos7Forest93Shapes
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option autoImplicit false

def primeSet : Finset ℕ := {3,5,7,11,13,17,19,23}
lemma primeSet_eq : primeSet = Finset.univ.image primes := by decide +kernel
lemma primeSet_properties : ∀ q ∈ primeSet,q.Prime ∧ Odd q ∧ q ≤ 23 := by decide +kernel
lemma cap_formula : ∀ j,caps j = if primes j = 3 then 2 else 1 := by decide +kernel
lemma prime_mem (j : Fin 8) : primes j ∈ primeSet := by rw [primeSet_eq]; exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
lemma cap_sum : (∑ j,caps j) = 9 := by decide +kernel

lemma profile {κ : Type} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a)
    (hinitial : ∀ p ∈ Finset.univ.biUnion (fun k => (m k).primeFactors),
      ∀ q,q.Prime → Odd q → q < p → q ∈ Finset.univ.biUnion (fun k => (m k).primeFactors))
    (hbound : (∑ p ∈ Finset.univ.biUnion (fun k => (m k).primeFactors),
      (Finset.univ.lcm m).factorization p*(p-1)) ≤ 92) :
    Finset.univ.biUnion (fun k => (m k).primeFactors) = primeSet ∧
      ∀ j,(Finset.univ.lcm m).factorization (primes j) = caps j := by
  classical
  let P := Finset.univ.biUnion (fun k => (m k).primeFactors)
  let N := Finset.univ.lcm m
  have hm0 (k : κ) : m k ≠ 0 := by have := (hc.2.1 k).1; omega
  have hN0 : N ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun k _ => hm0 k)
  have hprime (p : ℕ) (hp : p ∈ P) : p.Prime := by
    obtain ⟨k,_,hk⟩ := Finset.mem_biUnion.mp hp
    exact (Nat.mem_primeFactors.mp hk).1
  obtain ⟨k,p,hp,hpd,hplarge⟩ := Erdos7Capped19Schedule.arithmetic_large_prime m a hc
  have hp23 : 23 ≤ p := by
    by_contra hh
    have hp20 : 20 ≤ p := by omega
    have hp22 : p ≤ 22 := by omega
    interval_cases p <;> norm_num at hp
  have hpP : p ∈ P := Finset.mem_biUnion.mpr
    ⟨k,Finset.mem_univ _,Nat.mem_primeFactors.mpr ⟨hp,hpd,hm0 k⟩⟩
  have hsub : primeSet ⊆ P := by
    intro q hq
    obtain ⟨hqprime,hqodd,hqle⟩ := primeSet_properties q hq
    by_cases heq : q = p
    · exact heq ▸ hpP
    · exact hinitial p hpP q hqprime hqodd (by omega)
  have hfac (q : ℕ) (hq : q ∈ P) : 1 ≤ N.factorization q := by
    have hq' : q ∈ N.primeFactors := by
      simpa only [N,primeFactors_finset_lcm Finset.univ m (fun k _ => hm0 k)] using hq
    rw [← Nat.support_factorization,Finsupp.mem_support_iff] at hq'
    omega
  obtain ⟨l,hl⟩ := Erdos7No9Certificate.arithmetic_exists_nine m a hc
  have h9N : 9 ∣ N := hl.trans (Finset.dvd_lcm (Finset.mem_univ l))
  have h3fac : 2 ≤ N.factorization 3 :=
    (show Nat.Prime 3 by norm_num).pow_dvd_iff_le_factorization hN0 |>.mp h9N
  let base (q : ℕ) := if q ∈ primeSet then (if q = 3 then 4 else q-1) else 0
  have hbase : ∑ q ∈ P,base q = 92 := by
    have he : ∑ q ∈ primeSet,base q = ∑ q ∈ P,base q :=
      Finset.sum_subset hsub (fun q _ hq => by simp [base,hq])
    rw [← he]
    norm_num [base,primeSet]
  have hle (q : ℕ) (hq : q ∈ P) : base q ≤ N.factorization q*(q-1) := by
    by_cases hqQ : q ∈ primeSet
    · simp only [base,if_pos hqQ]
      by_cases heq : q = 3
      · subst q
        simp only [if_true,show (3:ℕ)-1 = 2 by omega]
        omega
      · rw [if_neg heq]
        have hh := Nat.mul_le_mul_right (q-1) (hfac q hq)
        simpa only [one_mul] using hh
    · simp [base,hqQ]
  have heq : ∀ q ∈ P,base q = N.factorization q*(q-1) := by
    apply (Finset.sum_eq_sum_iff_of_le hle).mp
    have hh := Finset.sum_le_sum hle
    change (∑ q ∈ P,N.factorization q*(q-1)) ≤ 92 at hbound
    omega
  have hPQ : P = primeSet := by
    apply Finset.Subset.antisymm _ hsub
    intro q hq
    by_contra hn
    have hh := heq q hq
    simp only [base,if_neg hn] at hh
    have hf := hfac q hq
    have hp := (hprime q hq).two_le
    have hz : 0 < q-1 := by omega
    have := Nat.mul_pos hf hz
    omega
  refine ⟨hPQ,?_⟩
  intro j
  have hjQ := prime_mem j
  have hh := heq (primes j) (hsub hjQ)
  rw [cap_formula]
  simp only [base,if_pos hjQ] at hh
  split_ifs with h3
  · rw [h3] at hh ⊢
    norm_num at hh
    change N.factorization 3 = 2
    omega
  · rw [if_neg h3] at hh
    have hp := (prime_properties.2 j).1.two_le
    have hz : 0 < primes j-1 := by omega
    nlinarith

lemma modulus_primeFactors_subset {κ : Type} [Fintype κ] (m : κ → ℕ)
    (hP : Finset.univ.biUnion (fun k => (m k).primeFactors) = primeSet) (k : κ) :
    (m k).primeFactors ⊆ Finset.univ.image primes := by
  rw [← primeSet_eq,← hP]
  exact Finset.subset_biUnion_of_mem (fun k => (m k).primeFactors) (Finset.mem_univ k)

#print axioms profile
end Erdos7Forest93Profile
