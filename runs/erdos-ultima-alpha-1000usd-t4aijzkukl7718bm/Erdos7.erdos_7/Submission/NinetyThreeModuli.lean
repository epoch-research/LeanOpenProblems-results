import Submission.Capped19Arithmetic
import Submission.No9Completion

/-! Combining the certified prime-19 and no9 obstructions with the
minimal-cardinality normal form and the digit-level Tarsi inequality. -/
namespace Erdos7NinetyThreeModuli
open scoped BigOperators
open Erdos7Reduction Erdos7Digits Erdos7Compression
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-- An initial-prime irredundant odd cover has digit weight at least92. -/
lemma initial_cover_weight {κ : Type} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a)
    (hinitial : ∀ p ∈ Finset.univ.biUnion (fun k => (m k).primeFactors),
      ∀ q,q.Prime → Odd q → q < p → q ∈ Finset.univ.biUnion (fun k => (m k).primeFactors)) :
    92 ≤ ∑ p ∈ Finset.univ.biUnion (fun k => (m k).primeFactors),
      (Finset.univ.lcm m).factorization p*(p-1) := by
  classical
  let P := Finset.univ.biUnion (fun k => (m k).primeFactors)
  let N := Finset.univ.lcm m
  let Q : Finset ℕ := {3,5,7,11,13,17,19,23}
  have hm0 (k : κ) : m k ≠ 0 := by have := (hc.2.1 k).1; omega
  have hN0 : N ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun k _ => hm0 k)
  obtain ⟨k,p,hp,hpd,hplarge⟩ := Erdos7Capped19Schedule.arithmetic_large_prime m a hc
  have hp23 : 23 ≤ p := by
    by_contra hh
    have hp20 : 20 ≤ p := by omega
    have hp22 : p ≤ 22 := by omega
    interval_cases p <;> norm_num at hp
  have hpP : p ∈ P := Finset.mem_biUnion.mpr
    ⟨k,Finset.mem_univ _,Nat.mem_primeFactors.mpr ⟨hp,hpd,hm0 k⟩⟩
  have hQ (q : ℕ) (hq : q ∈ Q) : q.Prime ∧ Odd q ∧ q ≤ 23 := by
    simp only [Q,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hsub : Q ⊆ P := by
    intro q hq
    obtain ⟨hqprime,hqodd,hqle⟩ := hQ q hq
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
  have hcalc : (∑ q ∈ Q,if q = 3 then 4 else q-1) = 92 := by norm_num [Q]
  calc
    92 = ∑ q ∈ Q,if q = 3 then 4 else q-1 := hcalc.symm
    _ ≤ ∑ q ∈ Q,N.factorization q*(q-1) := by
      apply Finset.sum_le_sum
      intro q hq
      by_cases heq : q = 3
      · subst q
        simp only [if_true,show (3:ℕ)-1 = 2 by omega]
        omega
      · rw [if_neg heq]
        have hh := Nat.mul_le_mul_right (q-1) (hfac q (hsub hq))
        simpa only [one_mul] using hh
    _ ≤ ∑ q ∈ P,N.factorization q*(q-1) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

/-- Every odd strict arithmetic covering system has at least93 classes. -/
theorem arithmetic_at_least_ninety_three {κ : Type} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a) :
    93 ≤ Fintype.card κ := by
  classical
  let N := Finset.univ.lcm m
  have hN0 : N ≠ 0 := Finset.lcm_ne_zero_iff.mpr
    (fun k _ => by have := (hc.2.1 k).1; omega)
  have hcover : HasOddArithmeticCover N (Fintype.card κ) :=
    ⟨Nat.pos_of_ne_zero hN0,κ,inferInstance,m,a,hc.1,hc.2.1,hc.2.2,
      fun k => Finset.dvd_lcm (Finset.mem_univ k),le_rfl⟩
  obtain ⟨ι,fι,n,b,hn,hcard,hmin,hclosed,hpriv,hinitial,hperiod⟩ :=
    exists_prime_initial_minimal_odd_cover N (Fintype.card κ) hcover
  letI : Fintype ι := fι
  have hw := initial_cover_weight n b hn hinitial
  have ht := arithmetic_irredundant_factorization_sum_bound n b
    (fun k => by have := (hn.2.1 k).1; omega) hn.2.2 hpriv
  omega

theorem at_least_ninety_three (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i,¬C.moduli i ≤ Ideal.span {2}) :
    letI := C.fintypeIndex
    93 ≤ Fintype.card C.ι := by
  letI := C.fintypeIndex
  exact arithmetic_at_least_ninety_three (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C,fun i => ⟨moduli_absNorm_gt_one C i,
      (ideal_not_le_two_iff _).mp (hodd i)⟩,arithmetic_cover C⟩

#print axioms arithmetic_at_least_ninety_three
#print axioms at_least_ninety_three
end Erdos7NinetyThreeModuli
