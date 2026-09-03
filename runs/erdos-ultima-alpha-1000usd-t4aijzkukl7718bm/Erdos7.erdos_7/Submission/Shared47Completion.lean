import Submission.Shared47Arithmetic

/-! The finite-47, ternary-exponent-two obstruction in arithmetic form.
This necessary condition does not settle the unrestricted odd covering problem. -/
namespace Erdos7Shared47Arithmetic
open scoped BigOperators
open Erdos7Shared47DistinctBoxes Erdos7Reduction
set_option maxHeartbeats 4000000
set_option autoImplicit false

lemma factorization_three_le_two (m : ℕ) (hm : m≠0) (h27 : ¬27 ∣ m) :
    m.factorization 3 ≤ 2 := by
  by_contra hh
  have he : 3 ≤ m.factorization 3 := by omega
  have hd := (show Nat.Prime 3 by norm_num).pow_dvd_iff_le_factorization (k:=3) hm
  exact h27 (by simpa only [show (3:ℕ)^3=27 from rfl] using hd.mpr he)

lemma small_odd_prime_mem (q : ℕ) (hq : q.Prime) (h3 : 3 ≤ q) (h47 : q ≤ 47) :
    ∃ i : Fin 14,primes i = q := by
  interval_cases q <;> norm_num [primes,Fin.exists_fin_succ] at *

/-- A restricted obstruction: either a ternary cube or a prime beyond 47 is necessary. -/
theorem arithmetic_alternative {κ : Type} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a) :
    (∃ k,27 ∣ m k) ∨ ∃ k q,q.Prime ∧ q ∣ m k ∧ 47 < q := by
  classical
  by_contra! hbad
  obtain ⟨h27,hno⟩ := hbad
  have hm0 (k : κ) : m k ≠ 0 := by have := (hc.2.1 k).1; omega
  let e (k : κ) (i : Fin 14) := (m k).factorization (primes i)
  let E (i : Fin 14) := Finset.univ.sup (fun k : κ => e k i)
  let D := E 1
  let F (j : Fin 12) := E j.succ.succ
  have hE (k : κ) (i : Fin 14) : e k i ≤ E i := Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)
  have heE (k : κ) (i : Fin 14) : e k i ≤ caps D F i := by
    cases i using Fin.cases with
    | zero => exact factorization_three_le_two (m k) (hm0 k) (h27 k)
    | succ j =>
      cases j using Fin.cases with
      | zero => exact (hE k 1).trans (Nat.le_succ _)
      | succ j => exact hE k j.succ.succ
  have hprod (k : κ) : m k = ∏ i,primes i^e k i := by
    let Q := Finset.univ.image primes
    have hsub : (m k).primeFactors ⊆ Q := by
      intro q hq
      obtain ⟨hqprime,hqdvd,hq0⟩ := Nat.mem_primeFactors.mp hq
      have hq2 : q ≠ 2 := by
        intro heq; subst q
        exact (Nat.not_even_iff_odd.mpr (hc.2.1 k).2) (even_iff_two_dvd.mpr hqdvd)
      have hq3 : 3 ≤ q := by have := hqprime.two_le; omega
      obtain ⟨i,hi⟩ := small_odd_prime_mem q hqprime hq3 (hno k q hqprime hqdvd)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
    have hh := Erdos7Compression.factorization_product_over_superset (m k) (hm0 k) Q hsub
    rw [Finset.prod_coe_sort Q (fun q => q^(m k).factorization q)] at hh
    rw [hh]
    exact Finset.prod_image (fun i _ j _ hij => primes_injective hij)
  have hei : Function.Injective e := by
    intro k l h
    apply hc.1
    rw [hprod k,hprod l,h]
  have he0 (k : κ) : ∃ i,e k i ≠ 0 := by
    by_contra! hz
    have hh := (hc.2.1 k).1
    rw [hprod k] at hh
    simp only [hz,pow_zero,Finset.prod_const_one] at hh
    omega
  apply prime_product_not_cover D F e hei he0 heE a
  simpa only [← hprod] using hc.2.2

theorem strict_alternative (C : StrictCoveringSystem ℤ) (hodd : ∀ i,¬C.moduli i ≤ Ideal.span {2}) :
    (∃ i,27 ∣ (C.moduli i).absNorm) ∨
      ∃ i q,q.Prime ∧ q ∣ (C.moduli i).absNorm ∧ 47 < q := by
  letI := C.fintypeIndex
  exact arithmetic_alternative (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C,fun i => ⟨moduli_absNorm_gt_one C i,
      (ideal_not_le_two_iff _).mp (hodd i)⟩,arithmetic_cover C⟩


#print axioms arithmetic_alternative
#print axioms strict_alternative
end Erdos7Shared47Arithmetic
