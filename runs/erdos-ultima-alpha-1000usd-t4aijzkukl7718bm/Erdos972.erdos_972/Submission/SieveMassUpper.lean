import Submission.SelbergLocalCost

/-! Uniform summability and elementary divisor bounds for the Selberg
normalizing weights. -/
namespace Erdos972SieveMassUpper

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Erdos972SelbergWeights Erdos972SelbergLocalCost

set_option maxHeartbeats 1500000

noncomputable def atomAF : ArithmeticFunction ℝ := ⟨sieveAtom, by simp [sieveAtom]⟩

lemma atomAF_apply (n : ℕ) : atomAF n = sieveAtom n := rfl

lemma atomAF_mult : atomAF.IsMultiplicative := by
  constructor
  · simp [atomAF, sieveAtom]
  · intro m n hc
    simp only [atomAF_apply, sieveAtom, isMultiplicative_moebius.map_mul_of_coprime hc,
      Nat.totient_mul hc, Int.cast_mul, Nat.cast_mul]
    ring

lemma sieveAtom_prime {p : ℕ} (hp : p.Prime) : sieveAtom p = 1/(p-1 : ℕ) := by
  simp [sieveAtom, moebius_apply_prime hp, Nat.totient_prime hp]

lemma squarefree_prime_product {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    Squarefree (∏ p ∈ P, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq)
  · intro p hp
    exact (hP p hp).squarefree

lemma sieveAtom_divisors {n : ℕ} (hn : Squarefree n) :
    (∑ d ∈ n.divisors, sieveAtom d) = (n : ℝ)/n.totient := by
  have he := atomAF_mult.prodPrimeFactors_one_add_of_squarefree hn
  simp only [atomAF_apply] at he
  rw [← he]
  have hterms : (∏ p ∈ n.primeFactors, (1+sieveAtom p)) =
      (∏ p ∈ n.primeFactors, (p : ℝ))/(∏ p ∈ n.primeFactors, ((p-1 : ℕ) : ℝ)) := by
    rw [← prod_div_distrib]
    apply prod_congr rfl
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    rw [sieveAtom_prime hprime]
    have hpm : ((p-1 : ℕ) : ℝ) = (p : ℝ)-1 := by simpa using (Nat.cast_sub (R := ℝ) hprime.one_le)
    have hp0 : (0 : ℝ) < (p-1 : ℕ) := Nat.cast_pos.mpr (by have := hprime.two_le; omega)
    field_simp
    linarith only [hpm]
  rw [hterms]
  have ht : (n.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn.ne_zero)).ne'
  have hprod : (∏ p ∈ n.primeFactors, ((p-1 : ℕ) : ℝ)) ≠ 0 := by
    apply ne_of_gt
    apply prod_pos
    intro p hp
    have hh := (Nat.prime_of_mem_primeFactors hp).two_le
    exact Nat.cast_pos.mpr (by omega)
  apply (div_eq_div_iff hprod ht).mpr
  have hh := Nat.totient_mul_prod_primeFactors n
  have hhR : (n.totient : ℝ)*(∏ p ∈ n.primeFactors, (p : ℝ)) =
      (n : ℝ)*(∏ p ∈ n.primeFactors, ((p-1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_prod] using congrArg (fun x : ℕ => (x : ℝ)) hh
  simpa only [mul_comm] using hhR

lemma sieveAtom_le_divisors {n : ℕ} (hn : 0 < n) :
    sieveAtom n ≤ (1/(n : ℝ))*(∑ d ∈ n.divisors, sieveAtom d) := by
  by_cases hs : Squarefree n
  · rw [sieveAtom_divisors hs, sieveAtom]
    have hmu : (μ n : ℝ)^2 = 1 := by exact_mod_cast moebius_sq_eq_one_of_squarefree hs
    rw [hmu]
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp only [div_eq_mul_inv]
    field_simp
    norm_num
  · rw [sieveAtom, moebius_eq_zero_of_not_squarefree hs]
    simp only [Int.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_div]
    exact mul_nonneg (by positivity) (sum_nonneg (fun _ _ => sieveAtom_nonneg _))

lemma reciprocal_adjacent_sum (R : ℕ) :
    (∑ n ∈ Ioc 1 R, (1 : ℝ)/((n : ℝ)*(n-1 : ℕ))) ≤ 1 := by
  by_cases hR : R ≤ 1
  · rw [Ioc_eq_empty_of_le hR, sum_empty]
    norm_num
  have hterms : (∑ n ∈ Ioc 1 R, (1 : ℝ)/((n : ℝ)*(n-1 : ℕ))) =
      ∑ j ∈ Ico 1 R, ((1 : ℝ)/j-1/(j+1 : ℕ)) := by
    rw [← Ico_add_one_add_one_eq_Ioc, ← sum_Ico_add' (fun n : ℕ => (1 : ℝ)/((n : ℝ)*(n-1 : ℕ))) 1 R 1]
    apply sum_congr rfl
    intro j hj
    obtain ⟨hj1, _⟩ := mem_Ico.mp hj
    have hjR : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  rw [hterms, sum_sub_distrib]
  have ht := sum_Ico_sub (fun j : ℕ => (1 : ℝ)/j) (by omega : 1 ≤ R)
  rw [sum_sub_distrib] at ht
  norm_num only [Nat.cast_one, div_one] at ht
  have hpos : 0 ≤ (1 : ℝ)/R := by positivity
  linarith only [ht, hpos]

noncomputable def atomOverN : ArithmeticFunction ℝ := atomAF.pdiv (ArithmeticFunction.id : ArithmeticFunction ℝ)

lemma atomOverN_apply (n : ℕ) : atomOverN n = sieveAtom n/n := rfl

lemma atomOverN_mult : atomOverN.IsMultiplicative :=
  atomAF_mult.pdiv isMultiplicative_id.natCast

/-- An absolute constant, independent of the sieve cutoff. -/
theorem sum_sieveAtom_div_le_three (R : ℕ) :
    (∑ n ∈ Ioc 0 R, sieveAtom n/n) ≤ 3 := by
  classical
  let P := (Ioc 0 R).filter Nat.Prime
  let Z := ∏ p ∈ P, p
  have hP : ∀ p ∈ P, p.Prime := fun _ hp => (mem_filter.mp hp).2
  have hZ : Squarefree Z := squarefree_prime_product hP
  have hfac : Z.primeFactors = P := Nat.primeFactors_prod hP
  have hprod : (∑ d ∈ Z.divisors, sieveAtom d/d) = ∏ p ∈ P, (1+(1:ℝ)/((p:ℝ)*(p-1:ℕ))) := by
    have hh := atomOverN_mult.prodPrimeFactors_one_add_of_squarefree hZ
    simp only [atomOverN_apply, hfac] at hh
    rw [← hh]
    apply prod_congr rfl
    intro p hp
    rw [sieveAtom_prime (hP p hp)]
    ring
  have hfilter : (∑ n ∈ Ioc 0 R, sieveAtom n/n) =
      ∑ n ∈ (Ioc 0 R).filter Squarefree, sieveAtom n/n := by
    rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    split_ifs with hs
    · rfl
    · simp [sieveAtom, moebius_eq_zero_of_not_squarefree hs]
  have hsub : (Ioc 0 R).filter Squarefree ⊆ Z.divisors := by
    intro n hn
    obtain ⟨hnI, hs⟩ := mem_filter.mp hn
    have hf : n.primeFactors ⊆ P := by
      intro p hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.pos_of_mem_primeFactors hp,
        (Nat.le_of_mem_primeFactors hp).trans (mem_Ioc.mp hnI).2⟩, Nat.prime_of_mem_primeFactors hp⟩
    refine Nat.mem_divisors.mpr ⟨?_, hZ.ne_zero⟩
    rw [← Nat.prod_primeFactors_of_squarefree hs]
    exact prod_dvd_prod_of_subset n.primeFactors P (fun p : ℕ => p) hf
  calc
    _ = _ := hfilter
    _ ≤ ∑ d ∈ Z.divisors, sieveAtom d/d :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => div_nonneg (sieveAtom_nonneg _) (Nat.cast_nonneg _))
    _ = _ := hprod
    _ ≤ ∏ p ∈ P, Real.exp ((1:ℝ)/((p:ℝ)*(p-1:ℕ))) := by
      apply prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp ((1:ℝ)/((p:ℝ)*(p-1:ℕ)))
    _ = Real.exp (∑ p ∈ P, (1:ℝ)/((p:ℝ)*(p-1:ℕ))) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 1 := by
      apply Real.exp_le_exp.mpr
      apply le_trans _ (reciprocal_adjacent_sum R)
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hpI, hpp⟩ := mem_filter.mp hp
        exact mem_Ioc.mpr ⟨hpp.one_lt, (mem_Ioc.mp hpI).2⟩
      · intro p hp _
        positivity
    _ ≤ 3 := by linarith only [Real.exp_one_lt_d9]

#print axioms sieveAtom_le_divisors
#print axioms sum_sieveAtom_div_le_three

end Erdos972SieveMassUpper
