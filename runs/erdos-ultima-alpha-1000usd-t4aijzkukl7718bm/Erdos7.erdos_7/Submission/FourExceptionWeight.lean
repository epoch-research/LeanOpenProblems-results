import Submission.ThreeDistinctExceptions
import Submission.FourExceptionScalarDefs

/-! Arithmetic weights for the prime-dependent cap schedule. -/
namespace Erdos7FourExceptionWeight
open scoped BigOperators
open Erdos7FourExceptionScalar (cap cap_bounds)
set_option maxHeartbeats 4000000

def weight (d : ℕ) : ℚ := (∏ p∈d.primeFactors, cap p)/d

lemma weight_nonneg (d : ℕ) : 0 ≤ weight d := by
  unfold weight
  apply div_nonneg
  · apply Finset.prod_nonneg
    intro p _
    have := (cap_bounds p).1
    linarith
  · positivity

lemma weight_eq_product (d : ℕ) (hd : d≠0) :
    weight d = ∏ q∈d.primeFactors, cap q/(q : ℚ)^d.factorization q := by
  have hh := Erdos7Compression.factorization_product_over_superset d hd d.primeFactors (Finset.Subset.refl _)
  rw [Finset.prod_coe_sort d.primeFactors (fun q => q^d.factorization q)] at hh
  have he : (d : ℚ)=∏ q∈d.primeFactors, (q : ℚ)^d.factorization q := by exact_mod_cast hh
  rw [Finset.prod_div_distrib,weight,← he]

lemma weight_le_old (d : ℕ) :
    weight d ≤ (16/15 : ℚ)*Erdos7WeightedExceptionArithmetic.weight d := by
  classical
  have hc (p : ℕ) : cap p ≤ (if p=5 then (16/15 : ℚ) else 1)*(5/4) := by
    unfold cap
    split_ifs <;> norm_num
  have hh := Finset.prod_le_prod
    (s := d.primeFactors) (f := cap) (g := fun p => (if p=5 then (16/15 : ℚ) else 1)*(5/4))
    (fun p _ => by have := (cap_bounds p).1; linarith) (fun p _ => hc p)
  rw [Finset.prod_mul_distrib,Finset.prod_const] at hh
  have hfactor : (∏ p∈d.primeFactors, if p=5 then (16/15 : ℚ) else 1) ≤ 16/15 := by
    by_cases h5 : 5∈d.primeFactors <;> simp [h5] <;> norm_num
  have hn := hh.trans (mul_le_mul_of_nonneg_right hfactor (by positivity))
  have hh' := div_le_div_of_nonneg_right hn (show (0 : ℚ) ≤ d by positivity)
  unfold weight Erdos7WeightedExceptionArithmetic.weight
  convert hh' using 1 <;> ring

lemma prime_weight (p : ℕ) (hp : p.Prime) : weight p=cap p/p := by
  simp [weight,hp.primeFactors]

lemma weight_outside (d : ℕ) (hd : 1 < d) (ho : Odd d) (h3 : ¬ 3 ∣ d)
    (h5 : d≠5) (h7 : d≠7) (h11 : d≠11) : weight d ≤ (5/52 : ℚ) := by
  by_cases hp : d.Prime
  · have hge : 13 ≤ d := by
      by_contra hn
      interval_cases d <;> norm_num at *
    have hc : cap d=(5/4 : ℚ) := by simp [cap,h5,h7]
    rw [prime_weight d hp,hc]
    have hge' : (13 : ℚ) ≤ d := by exact_mod_cast hge
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < d)).mpr
    linarith
  · have hh := (weight_le_old d).trans
      (mul_le_mul_of_nonneg_left
        (Erdos7ThreeDistinctExceptions.composite_weight_le d hd ho h3 hp) (by norm_num : (0 : ℚ) ≤ 16/15))
    linarith

lemma four_distinct_weight {J : Type*} [Fintype J]
    (d : J → ℕ) (hinj : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (h3 : ∀ j, ¬ 3 ∣ d j)
    (hJ : Fintype.card J ≤ 4) : (∑ j, weight (d j)) ≤ (9728/15015 : ℚ) := by
  classical
  have hb (j : J) : weight (d j) ≤ (5/52 : ℚ) +
      (if d j=5 then 4/15-5/52 else 0) +
      (if d j=7 then 6/35-5/52 else 0) +
      (if d j=11 then 5/44-5/52 else 0) := by
    by_cases h5 : d j=5
    · rw [h5]
      norm_num [prime_weight 5 (by decide),cap]
    · by_cases h7 : d j=7
      · rw [h7]
        norm_num [prime_weight 7 (by decide),cap]
      · by_cases h11 : d j=11
        · rw [h11]
          norm_num [prime_weight 11 (by decide),cap]
        · simpa only [if_neg h5,if_neg h7,if_neg h11,add_zero] using
            weight_outside (d j) (hd j).1 (hd j).2 (h3 j) h5 h7 h11
  have he (p : ℕ) (c : ℚ) (hc : 0 ≤ c) :
      (∑ j : J, if d j=p then c else 0) ≤ c := by
    have hcard : (Finset.univ.filter (fun j : J => d j=p)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro j hj k hk
      exact hinj ((Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hk).2.symm)
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    have hcard' : ((Finset.univ.filter (fun j : J => d j=p)).card : ℚ) ≤ 1 := by exact_mod_cast hcard
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcard' hc
  have hh := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hb j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have h5 := he 5 (4/15-5/52) (by norm_num)
  have h7 := he 7 (6/35-5/52) (by norm_num)
  have h11 := he 11 (5/44-5/52) (by norm_num)
  have hJ' : (Fintype.card J : ℚ) ≤ 4 := by exact_mod_cast hJ
  linarith

#print axioms four_distinct_weight
end Erdos7FourExceptionWeight
