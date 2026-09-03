import Submission.Forest93Arithmetic

/-! The verified forest overlap strengthens the class-count obstruction to94. -/
namespace Erdos7NinetyFourModuli
open scoped BigOperators
open Erdos7Reduction Erdos7Digits Erdos7Compression
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option Elab.async false

/-- Every odd strict arithmetic covering system has at least94 classes. -/
theorem arithmetic_at_least_ninety_four {κ : Type} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a) :
    94 ≤ Fintype.card κ := by
  classical
  by_contra h
  have h93 : Fintype.card κ ≤ 93 := by omega
  let N := Finset.univ.lcm m
  have hN0 : N ≠ 0 := Finset.lcm_ne_zero_iff.mpr
    (fun k _ => by have := (hc.2.1 k).1; omega)
  have hcover : HasOddArithmeticCover N (Fintype.card κ) :=
    ⟨Nat.pos_of_ne_zero hN0,κ,inferInstance,m,a,hc.1,hc.2.1,hc.2.2,
      fun k => Finset.dvd_lcm (Finset.mem_univ k),le_rfl⟩
  obtain ⟨ι,fι,n,b,hn,hcard,hmin,hclosed,hpriv,hinitial,hperiod⟩ :=
    exists_prime_initial_minimal_odd_cover N (Fintype.card κ) hcover
  letI : Fintype ι := fι
  have hcard93 : Fintype.card ι ≤ 93 := hcard.trans h93
  have ht := arithmetic_irredundant_factorization_sum_bound n b
    (fun k => by have := (hn.2.1 k).1; omega) hn.2.2 hpriv
  obtain ⟨hP,hE⟩ := Erdos7Forest93Profile.profile n b hn hinitial (by omega)
  exact Erdos7Forest93Arithmetic.profile_not_cover n b hn hclosed hpriv hP hE hcard93

theorem at_least_ninety_four (C : StrictCoveringSystem ℤ)
    (hodd : ∀ i,¬C.moduli i ≤ Ideal.span {2}) :
    letI := C.fintypeIndex
    94 ≤ Fintype.card C.ι := by
  letI := C.fintypeIndex
  exact arithmetic_at_least_ninety_four (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C,fun i => ⟨moduli_absNorm_gt_one C i,
      (ideal_not_le_two_iff _).mp (hodd i)⟩,arithmetic_cover C⟩

#print axioms arithmetic_at_least_ninety_four
#print axioms at_least_ninety_four
end Erdos7NinetyFourModuli
