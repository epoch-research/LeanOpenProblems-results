import Submission.Forest93Profile

/-! Arithmetic recognition of the finite exponent rectangle. -/
namespace Erdos7Forest93ShapeArithmetic
open scoped BigOperators
open Erdos7Reduction Erdos7Digits Erdos7Compression
open Erdos7Forest93Certificate Erdos7Forest93Shapes Erdos7Forest93Profile
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option Elab.async false

def fromExponent (e : Fin 8 → ℕ) (he : ∀ j,e j ≤ caps j) : Index :=
  index (⟨e 0,by have := he 0; change e 0 ≤ 2 at this; omega⟩,
    fun j => ⟨e j.succ,by
      have := he j.succ
      have hc : caps j.succ = 1 := by fin_cases j <;> rfl
      rw [hc] at this
      omega⟩)
lemma exponent_fromExponent (e : Fin 8 → ℕ) (he : ∀ j,e j ≤ caps j) :
    exponent (fromExponent e he) = e := by
  rw [fromExponent,exponent_index]
  funext j
  induction j using Fin.cases <;> rfl

lemma mixed_has_divisor : ∀ i,mixed i → ∃ j,primes j ∣ modulus i ∧
    primes j ≠ 1 ∧ primes j ≠ modulus i := by decide +kernel
lemma nonmixed_codes : ∀ i,¬mixed i → modulus i = 1 ∨ modulus i = 9 ∨
    ∃ j,modulus i = primes j ∧ exponent i j = 1 := by decide +kernel
lemma mixed_not_prime (i : Index) (hi : mixed i) : ¬(modulus i).Prime := by
  intro hp
  obtain ⟨j,hd,h1,hm⟩ := mixed_has_divisor i hi
  exact (hp.eq_one_or_self_of_dvd _ hd).elim h1 hm
lemma nonmixed_classification (i : Index) (hi : ¬mixed i) :
    modulus i = 1 ∨ modulus i = 9 ∨ (modulus i).Prime := by
  rcases nonmixed_codes i hi with h | h | ⟨j,hj,_⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (hj ▸ (prime_properties.2 j).1))
lemma prime_classification (i : Index) (hi : (modulus i).Prime) :
    ∃ j,modulus i = primes j ∧ exponent i j = 1 := by
  rcases nonmixed_codes i (fun hm => mixed_not_prime i hm hi) with h | h | h
  · rw [h] at hi; norm_num at hi
  · rw [h] at hi; norm_num at hi
  · exact h
lemma exponent_prime_dvd (i : Index) (j : Fin 8) (hj : exponent i j ≠ 0) : primes j ∣ modulus i :=
  (dvd_pow_self (primes j) hj).trans
    (Finset.dvd_prod_of_mem (fun j => primes j^exponent i j) (Finset.mem_univ j))
lemma exponent_pow_dvd (i : Index) (j : Fin 8) : primes j^exponent i j ∣ modulus i :=
  Finset.dvd_prod_of_mem (fun j => primes j^exponent i j) (Finset.mem_univ j)

lemma exists_encoding {κ : Type} [Fintype κ] (m : κ → ℕ)
    (hm0 : ∀ k,m k ≠ 0) (hinj : Function.Injective m)
    (hP : Finset.univ.biUnion (fun k => (m k).primeFactors) = primeSet)
    (hE : ∀ j,(Finset.univ.lcm m).factorization (primes j) = caps j) :
    ∃ f : κ → Index,Function.Injective f ∧ (∀ k,modulus (f k) = m k) ∧
      ∀ k j,exponent (f k) j = (m k).factorization (primes j) := by
  classical
  have hN0 : Finset.univ.lcm m ≠ 0 := Finset.lcm_ne_zero_iff.mpr (fun k _ => hm0 k)
  have he (k : κ) (j : Fin 8) : (m k).factorization (primes j) ≤ caps j := by
    rw [← hE j]
    exact (Nat.factorization_le_iff_dvd (hm0 k) hN0).mpr
      (Finset.dvd_lcm (Finset.mem_univ k)) (primes j)
  let f (k : κ) := fromExponent (fun j => (m k).factorization (primes j)) (he k)
  have hf (k : κ) : exponent (f k) = fun j => (m k).factorization (primes j) := exponent_fromExponent _ _
  have hm (k : κ) : modulus (f k) = m k := by
    unfold modulus
    rw [hf]
    have hh := factorization_product_over_superset (m k) (hm0 k)
      (Finset.univ.image primes) (modulus_primeFactors_subset m hP k)
    rw [Finset.prod_coe_sort (Finset.univ.image primes) (fun q => q^(m k).factorization q)] at hh
    exact (Finset.prod_image (s := Finset.univ) (g := primes)
      (f := fun q => q^(m k).factorization q)
      (fun i _ j _ hij => prime_properties.1 hij)).symm.trans hh.symm
  refine ⟨f,?_,hm,fun k j => congrFun (hf k) j⟩
  intro k l h
  apply hinj
  rw [← hm k,← hm l,h]

#print axioms exists_encoding
#print axioms nonmixed_classification
end Erdos7Forest93ShapeArithmetic
