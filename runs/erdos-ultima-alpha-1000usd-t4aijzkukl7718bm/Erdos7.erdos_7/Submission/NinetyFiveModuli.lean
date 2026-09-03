import Submission.Forest105Arithmetic

/-! A global95-class necessary condition. This does not settle Erdos7. -/
namespace Erdos7NinetyFiveModuli
open scoped BigOperators
open Erdos7Reduction Erdos7Digits Erdos7Compression
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option Elab.async false

lemma digit_weight_even {κ : Type} [Fintype κ]
    (m : κ → ℕ) (hm : ∀ k, Odd (m k)) :
    Even (∑ p ∈ Finset.univ.biUnion (fun k => (m k).primeFactors),
      (Finset.univ.lcm m).factorization p*(p-1)) := by
  classical
  apply Finset.even_sum
  intro p hp
  obtain ⟨k,_,hpk⟩ := Finset.mem_biUnion.mp hp
  have hodd : Odd p := Odd.of_dvd_nat (hm k) (Nat.mem_primeFactors.mp hpk).2.1
  have he : Even (p-1) := by
    obtain ⟨r,hr⟩ := hodd
    exact ⟨r,by omega⟩
  exact he.mul_left _

/-- Every odd strict arithmetic covering system has at least95 classes. -/
theorem arithmetic_at_least_ninety_five {κ : Type} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a) :
    95 ≤ Fintype.card κ := by
  classical
  by_contra h
  have h94 : Fintype.card κ ≤ 94 := by omega
  let N := Finset.univ.lcm m
  have hN0 : N ≠ 0 := Finset.lcm_ne_zero_iff.mpr
    (fun k _ => by have := (hc.2.1 k).1; omega)
  have hcover : HasOddArithmeticCover N (Fintype.card κ) :=
    ⟨Nat.pos_of_ne_zero hN0,κ,inferInstance,m,a,hc.1,hc.2.1,hc.2.2,
      fun k => Finset.dvd_lcm (Finset.mem_univ k),le_rfl⟩
  obtain ⟨ι,fι,n,b,hn,hcard,hmin,hclosed,hpriv,hinitial,hperiod⟩ :=
    exists_prime_initial_minimal_odd_cover N (Fintype.card κ) hcover
  letI : Fintype ι := fι
  have hcard94 : Fintype.card ι ≤ 94 := hcard.trans h94
  have ht := arithmetic_irredundant_factorization_sum_bound n b
    (fun k => by have := (hn.2.1 k).1; omega) hn.2.2 hpriv
  have hev := digit_weight_even n (fun k => (hn.2.1 k).2)
  have hweight : (∑ p ∈ Finset.univ.biUnion (fun k => (n k).primeFactors),
      (Finset.univ.lcm n).factorization p*(p-1)) ≤ 92 := by
    obtain ⟨r,hr⟩ := hev
    omega
  obtain ⟨hP,hE⟩ := Erdos7Forest93Profile.profile n b hn hinitial hweight
  exact Erdos7Forest105.profile_not_cover n b hn hclosed hpriv hP hE (by omega)

theorem at_least_ninety_five (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i,¬C.moduli i ≤ Ideal.span {2}) :
    letI := C.fintypeIndex
    95 ≤ Fintype.card C.ι := by
  letI := C.fintypeIndex
  exact arithmetic_at_least_ninety_five (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C,fun i => ⟨moduli_absNorm_gt_one C i,
      (ideal_not_le_two_iff _).mp (hodd i)⟩,arithmetic_cover C⟩

#print axioms digit_weight_even
#print axioms arithmetic_at_least_ninety_five
#print axioms at_least_ninety_five
end Erdos7NinetyFiveModuli
