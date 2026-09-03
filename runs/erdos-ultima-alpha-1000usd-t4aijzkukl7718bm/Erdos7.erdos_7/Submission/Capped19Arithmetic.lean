import Submission.Capped19Boxes

/-! Arithmetic obstruction for odd distinct covers using only primes ≤ 19.
The unrestricted Erdős conjecture is not asserted here. -/
namespace Erdos7Capped19Schedule
open scoped BigOperators
open Erdos7CompleteFamilyModel Erdos7Reduction Erdos7StarSieve
set_option maxHeartbeats 3000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

lemma primes_coprime : Pairwise (Function.onFun Nat.Coprime primes) := by
  unfold Pairwise Function.onFun
  decide +kernel
lemma primes_injective : Function.Injective primes := by decide +kernel

/-- Arbitrary finite exponent caps, including zero exponents, are allowed. -/
theorem prime_product_not_cover {κ : Type} [Fintype κ]
    (E : Fin 7 → ℕ) (e : κ → Fin 7 → ℕ) (he : Function.Injective e)
    (he0 : ∀ k,∃ i,e k i ≠ 0) (heE : ∀ k i,e k i ≤ E i) (a : κ → ℤ) :
    ¬ (∀ z : ℤ,∃ k,((∏ i,primes i^e k i:ℕ):ℤ) ∣ z-a k) := by
  classical
  intro hcover
  letI (i : Fin 7) : NeZero (primes i) := ⟨by have := primes_gt_one i; omega⟩
  let A (i : Fin 7) := ZMod (primes i^E i)
  let f (k : κ) (i : Fin 7) := ZMod.castHom (pow_dvd_pow (primes i) (heE k i))
    (ZMod (primes i^e k i))
  let B (k : κ) (i : Fin 7) : Finset (A i) :=
    Finset.univ.filter (fun x => f k i x = (a k:ZMod (primes i^e k i)))
  let ρ (i : Fin 7) (_ : A i) : ℝ := 1/Fintype.card (A i)
  have hρ (i : Fin 7) (x : A i) : 0 ≤ ρ i x := by dsimp only [ρ]; positivity
  have hρmass (i : Fin 7) : (∑ y,ρ i y) = 1 := by
    simp only [ρ,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hn : (Fintype.card (A i):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
    field_simp
  have hd (k : κ) (i : Fin 7) (_ : e k i ≠ 0) :
      (∑ y,if y ∈ B k i then ρ i y else 0) ≤ 1/(primes i:ℝ)^(e k i) := by
    have hh := surjective_fiber_card_rat (f k i).toAddMonoidHom
      (ZMod.castHom_surjective (pow_dvd_pow (primes i) (heE k i))) (a k)
    change ((B k i).card:ℚ) = _ at hh
    have hreal : ((B k i).card:ℝ) = (Fintype.card (A i):ℝ)/(primes i:ℝ)^(e k i) := by
      have hh' : ((B k i).card:ℚ) = (Fintype.card (A i):ℚ)/(primes i:ℚ)^(e k i) := by
        simpa only [A,ZMod.card,Nat.cast_pow] using hh
      have hcast := congrArg (fun q : ℚ => (q:ℝ)) hh'
      simpa only [Rat.cast_natCast,Rat.cast_div,Rat.cast_pow] using hcast
    have hn : (Fintype.card (A i):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
    simp only [ρ,Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul,hreal]
    exact (by field_simp :
      (Fintype.card (A i):ℝ)/(primes i:ℝ)^(e k i)*(1/Fintype.card (A i)) =
        1/(primes i:ℝ)^(e k i)).le
  apply distinct_box_not_cover A E e he heE he0 B ρ hρ hρmass hd
  intro x
  let z := Nat.chineseRemainderOfFinset (fun i => (x i).val) (fun i => primes i^E i) Finset.univ
    (fun i _ => pow_ne_zero _ (NeZero.ne _))
    (fun i _ j _ hij => (primes_coprime hij).pow _ _)
  have hz (i : Fin 7) : (z.val:A i) = x i := by
    rw [← ZMod.natCast_zmod_val (x i)]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (z.property i (Finset.mem_univ _))
  obtain ⟨k,hk⟩ := hcover (z.val:ℤ)
  refine ⟨k,fun i _ => ?_⟩
  have hpi : primes i^e k i ∣ ∏ j,primes j^e k j :=
    Finset.dvd_prod_of_mem (fun j => primes j^e k j) (Finset.mem_univ i)
  have hpi' : ((primes i^e k i:ℕ):ℤ) ∣ ((∏ j,primes j^e k j:ℕ):ℤ) := by exact_mod_cast hpi
  have hqi := hpi'.trans hk
  simp only [B,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [← hz i,map_natCast]
  symm
  simpa only [Int.cast_natCast] using
    (ZMod.intCast_eq_intCast_iff_dvd_sub (a k) (z.val:ℤ) (primes i^e k i)).mpr hqi

lemma small_odd_prime_mem (q : ℕ) (hq : q.Prime) (h3 : 3 ≤ q) (h19 : q ≤ 19) :
    ∃ i : Fin 7,primes i = q := by
  interval_cases q <;> norm_num [primes,Fin.exists_fin_succ] at *

/-- An unrestricted odd cover must contain a modulus with a prime factor > 19. -/
theorem arithmetic_large_prime {κ : Type} [Fintype κ]
    (m : κ → ℕ) (a : κ → ℤ) (hc : IsOddArithmeticCover m a) :
    ∃ k q,q.Prime ∧ q ∣ m k ∧ 19 < q := by
  classical
  by_contra! hno
  have hm0 (k : κ) : m k ≠ 0 := by have := (hc.2.1 k).1; omega
  let e (k : κ) (i : Fin 7) := (m k).factorization (primes i)
  let E (i : Fin 7) := Finset.univ.sup (fun k : κ => e k i)
  have heE (k : κ) (i : Fin 7) : e k i ≤ E i := Finset.le_sup (f := fun k => e k i) (Finset.mem_univ k)
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
  apply prime_product_not_cover E e hei he0 heE a
  simpa only [← hprod] using hc.2.2

theorem large_prime (C : StrictCoveringSystem ℤ) (hodd : ∀ i,¬C.moduli i ≤ Ideal.span {2}) :
    ∃ i q,q.Prime ∧ q ∣ (C.moduli i).absNorm ∧ 19 < q := by
  letI := C.fintypeIndex
  exact arithmetic_large_prime (fun i => (C.moduli i).absNorm) C.residue
    ⟨moduli_absNorm_injective C,fun i => ⟨moduli_absNorm_gt_one C i,
      (ideal_not_le_two_iff _).mp (hodd i)⟩,arithmetic_cover C⟩

#print axioms arithmetic_large_prime
#print axioms large_prime
end Erdos7Capped19Schedule
