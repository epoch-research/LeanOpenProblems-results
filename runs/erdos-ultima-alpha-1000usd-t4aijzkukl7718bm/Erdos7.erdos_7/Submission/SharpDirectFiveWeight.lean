import Submission.FiveExceptionWeights
import Submission.SharpDirectFiveScalarDefs

/-! Arithmetic weights for the prime-dependent cap schedule. -/
namespace Erdos7SharpDirectFiveWeight
open scoped BigOperators
open Erdos7SharpDirectFiveScalar (cap cap_bounds)
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
    weight d ≤ (16/11 : ℚ)*Erdos7WeightedExceptionArithmetic.weight d := by
  classical
  have hc (p : ℕ) : cap p ≤ (if p=5 then (16/11 : ℚ) else 1)*(5/4) := by
    unfold cap
    split_ifs <;> norm_num
  have hh := Finset.prod_le_prod
    (s := d.primeFactors) (f := cap) (g := fun p => (if p=5 then (16/11 : ℚ) else 1)*(5/4))
    (fun p _ => by have := (cap_bounds p).1; linarith) (fun p _ => hc p)
  rw [Finset.prod_mul_distrib,Finset.prod_const] at hh
  have hfactor : (∏ p∈d.primeFactors, if p=5 then (16/11 : ℚ) else 1) ≤ 16/11 := by
    by_cases h5 : 5∈d.primeFactors <;> simp [h5] <;> norm_num
  have hn := hh.trans (mul_le_mul_of_nonneg_right hfactor (by positivity))
  have hh' := div_le_div_of_nonneg_right hn (show (0 : ℚ) ≤ d by positivity)
  unfold weight Erdos7WeightedExceptionArithmetic.weight
  convert hh' using 1 <;> ring

lemma prime_weight (p : ℕ) (hp : p.Prime) : weight p=cap p/p := by
  simp [weight,hp.primeFactors]

lemma weight_outside (d : ℕ) (hd : 1 < d) (ho : Odd d) (h3 : ¬ 3 ∣ d)
    (h5 : d≠5) (h7 : d≠7) (h11 : d≠11) : weight d ≤ (1/10 : ℚ) := by
  by_cases hp : d.Prime
  · have hge : 13 ≤ d := by
      by_contra hn
      interval_cases d <;> norm_num at *
    have hc : cap d=(5/4 : ℚ) := by simp [cap,h5]
    rw [prime_weight d hp,hc]
    have hge' : (13 : ℚ) ≤ d := by exact_mod_cast hge
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < d)).mpr
    linarith
  · have hh := (weight_le_old d).trans (mul_le_mul_of_nonneg_left
      (Erdos7ThreeDistinctExceptions.composite_weight_le d hd ho h3 hp)
      (by norm_num : (0 : ℚ) ≤ 16/11))
    linarith

lemma four_missing_five_weight {J : Type*} [Fintype J]
    (d : J → ℕ) (hinj : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (h3 : ∀ j, ¬ 3 ∣ d j)
    (h5 : ∀ j, d j≠5) (hJ : Fintype.card J ≤ 4) :
    (∑ j, weight (d j)) ≤ (1/2 : ℚ) := by
  classical
  have hb (j : J) : weight (d j) ≤ (1/10 : ℚ)+
      (if d j=7 then 5/28-1/10 else 0)+(if d j=11 then 5/44-1/10 else 0) := by
    by_cases h7 : d j=7
    · rw [h7]; norm_num [prime_weight 7 (by decide),cap]
    by_cases h11 : d j=11
    · rw [h11]; norm_num [prime_weight 11 (by decide),cap]
    simpa only [if_neg h7,if_neg h11,add_zero] using
      weight_outside (d j) (hd j).1 (hd j).2 (h3 j) (h5 j) h7 h11
  have hh := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hb j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have h7 := Erdos7FiveExceptionWeights.indicator_sum_le d hinj 7 (5/28-1/10) (by norm_num)
  have h11 := Erdos7FiveExceptionWeights.indicator_sum_le d hinj 11 (5/44-1/10) (by norm_num)
  have hJ' : (Fintype.card J : ℚ) ≤ 4 := by exact_mod_cast hJ
  linarith

lemma old_weight_missing_five (d : ℕ) (hd : 1 < d) (ho : Odd d) (h3 : ¬ 3 ∣ d)
    (h5 : d≠5) : Erdos7WeightedExceptionArithmetic.weight d ≤ (5/28 : ℚ) := by
  by_cases hp : d.Prime
  · have hge : 7 ≤ d := by
      by_contra hn
      interval_cases d <;> norm_num at *
    rw [Erdos7ThreeDistinctExceptions.prime_weight d hp]
    have hge' : (7 : ℚ) ≤ d := by exact_mod_cast hge
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < d)).mpr
    linarith
  · exact (Erdos7ThreeDistinctExceptions.composite_weight_le d hd ho h3 hp).trans (by norm_num)

lemma old_composite_weight_le (d : ℕ) (hd : 1 < d) (ho : Odd d) (h3 : ¬ 3 ∣ d)
    (hp : ¬ d.Prime) : Erdos7WeightedExceptionArithmetic.weight d ≤ (1/20 : ℚ) := by
  obtain ⟨u,v,hu,hv,he⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega : 2 ≤ d)).mp hp
  have hu1 : 1 < u := by nlinarith
  have hv1 : 1 < v := by nlinarith
  have hud : u ∣ d := he ▸ dvd_mul_right u v
  have hvd : v ∣ d := he ▸ dvd_mul_left v u
  have hwu := Erdos7ThreeDistinctExceptions.weight_le_quarter u hu1
    (ho.of_dvd_nat hud) (fun hh => h3 (hh.trans hud))
  have hwv := Erdos7ThreeDistinctExceptions.weight_le_quarter v hv1
    (ho.of_dvd_nat hvd) (fun hh => h3 (hh.trans hvd))
  have hh := Erdos7ThreeDistinctExceptions.weight_mul_le u v (by omega) (by omega)
  rw [he] at hh
  by_cases hu5 : u=5
  · by_cases hv5 : v=5
    · have hd25 : d=25 := by simpa only [hu5,hv5] using he.symm
      rw [hd25]
      decide +kernel
    · have hsmall := old_weight_missing_five v hv1 (ho.of_dvd_nat hvd)
        (fun hh => h3 (hh.trans hvd)) hv5
      have hb := mul_le_mul hwu hsmall (Erdos7ThreeDistinctExceptions.weight_nonneg v)
        (by norm_num : (0 : ℚ) ≤ 1/4)
      linarith
  · have hsmall := old_weight_missing_five u hu1 (ho.of_dvd_nat hud)
      (fun hh => h3 (hh.trans hud)) hu5
    have hb := mul_le_mul hsmall hwv (Erdos7ThreeDistinctExceptions.weight_nonneg v)
      (by norm_num : (0 : ℚ) ≤ 5/28)
    linarith

lemma weight_outside_four (d : ℕ) (hd : 1 < d) (ho : Odd d) (h3 : ¬ 3 ∣ d)
    (h5 : d≠5) (h7 : d≠7) (h11 : d≠11) (h13 : d≠13) : weight d ≤ (5/68 : ℚ) := by
  by_cases hp : d.Prime
  · have hge : 17 ≤ d := by
      by_contra hn
      interval_cases d <;> norm_num at *
    have hc : cap d=(5/4 : ℚ) := by simp [cap,h5]
    rw [prime_weight d hp,hc]
    have hge' : (17 : ℚ) ≤ d := by exact_mod_cast hge
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < d)).mpr
    linarith
  · have hh := (weight_le_old d).trans (mul_le_mul_of_nonneg_left
      (old_composite_weight_le d hd ho h3 hp) (by norm_num : (0 : ℚ) ≤ 16/11))
    linarith

lemma five_missing_five_weight {J : Type*} [Fintype J]
    (d : J → ℕ) (hinj : Function.Injective d)
    (hd : ∀ j, 1 < d j ∧ Odd (d j)) (h3 : ∀ j, ¬ 3 ∣ d j)
    (h5 : ∀ j, d j≠5) (hJ : Fintype.card J ≤ 5) :
    (∑ j, weight (d j)) ≤ (11/20 : ℚ) := by
  classical
  have hb (j : J) : weight (d j) ≤ (5/68 : ℚ)+
      (if d j=7 then 5/28-5/68 else 0)+(if d j=11 then 5/44-5/68 else 0)+
      (if d j=13 then 5/52-5/68 else 0) := by
    by_cases h7 : d j=7
    · rw [h7]; norm_num [prime_weight 7 (by decide),cap]
    by_cases h11 : d j=11
    · rw [h11]; norm_num [prime_weight 11 (by decide),cap]
    by_cases h13 : d j=13
    · rw [h13]; norm_num [prime_weight 13 (by decide),cap]
    simpa only [if_neg h7,if_neg h11,if_neg h13,add_zero] using
      weight_outside_four (d j) (hd j).1 (hd j).2 (h3 j) (h5 j) h7 h11 h13
  have hh := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hb j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have h7 := Erdos7FiveExceptionWeights.indicator_sum_le d hinj 7 (5/28-5/68) (by norm_num)
  have h11 := Erdos7FiveExceptionWeights.indicator_sum_le d hinj 11 (5/44-5/68) (by norm_num)
  have h13 := Erdos7FiveExceptionWeights.indicator_sum_le d hinj 13 (5/52-5/68) (by norm_num)
  have hJ' : (Fintype.card J : ℚ) ≤ 5 := by exact_mod_cast hJ
  linarith

#print axioms old_composite_weight_le
#print axioms five_missing_five_weight
end Erdos7SharpDirectFiveWeight
