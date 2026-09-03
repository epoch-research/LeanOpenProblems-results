import Submission.Work

/-!
# Restrictions on totient multiplicity from the 2-adic valuation

These are unconditional upper bounds on restricted families, not a settlement
of Erdős problem 821.
-/

open Nat Filter
open scoped Classical

namespace Erdos821

lemma polynomial_le_constant_mul_two_pow (e k : ℕ) :
    (e + 1) ^ k ≤ (k.factorial * 2 ^ k) * 2 ^ e := by
  calc
    (e + 1) ^ k ≤ (e + 1).ascFactorial k := Nat.pow_succ_le_ascFactorial _ _
    _ = k.factorial * (e + k).choose k := Nat.ascFactorial_eq_factorial_mul_choose _ _
    _ ≤ k.factorial * 2 ^ (e + k) := Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _)
    _ = _ := by rw [pow_add]; ring

/-- A uniform power bound for the divisor-counting function, with a fully
explicit constant depending only on the power. -/
lemma card_divisors_pow_le (n k : ℕ) (hn : n ≠ 0) :
    n.divisors.card ^ k ≤ (k.factorial * 2 ^ k) ^ (2 ^ k) * n := by
  let C := k.factorial * 2 ^ k
  let B := 2 ^ k
  have hC : 1 ≤ C := Nat.one_le_iff_ne_zero.mpr (by dsimp [C]; positivity)
  have hlocal (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p + 1) ^ k ≤ (if p < B then C else 1) * p ^ n.factorization p := by
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hsmall : p < B
    · rw [if_pos hsmall]
      exact (polynomial_le_constant_mul_two_pow _ _).trans
        (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hp2 _))
    · rw [if_neg hsmall, one_mul]
      calc
        (n.factorization p + 1) ^ k ≤ (2 ^ n.factorization p) ^ k :=
          Nat.pow_le_pow_left (Nat.succ_le_of_lt Nat.lt_two_pow_self) _
        _ = B ^ n.factorization p := by dsimp [B]; rw [pow_right_comm]
        _ ≤ _ := Nat.pow_le_pow_left (Nat.le_of_not_gt hsmall) _
  have hsmallcard : (n.primeFactors.filter (fun p => p < B)).card ≤ B := by
    calc
      _ ≤ (Finset.range B).card := Finset.card_le_card (by
        intro p hp; exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = B := Finset.card_range _
  have hfac : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    simpa only [Finsupp.prod, Nat.support_factorization] using Nat.factorization_prod_pow_eq_self hn
  rw [Nat.card_divisors hn, ← Finset.prod_pow]
  calc
    (∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ k) ≤
        ∏ p ∈ n.primeFactors, (if p < B then C else 1) * p ^ n.factorization p :=
      Finset.prod_le_prod' hlocal
    _ = C ^ (n.primeFactors.filter (fun p => p < B)).card * n := by
      rw [Finset.prod_mul_distrib, ← Finset.prod_filter, Finset.prod_const,
        hfac]
    _ ≤ C ^ B * n := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hC hsmallcard)

/-- Each odd prime in an admissible support supplies a distinct factor of two
in the product of prime predecessors dividing the output. -/
lemma admissibleSupport_card_le_two_valuation {n : ℕ} (hn : 0 < n)
    {S : Finset ℕ} (hS : S ∈ admissibleSupports n) : S.card ≤ n.factorization 2 + 1 := by
  classical
  obtain ⟨hSp, hprod, _⟩ := Finset.mem_filter.mp hS
  have hsub := Finset.mem_powerset.mp hSp
  have htwo : 2 ^ (S.erase 2).card ∣ ∏ p ∈ S.erase 2, (p - 1) := by
    rw [← Finset.prod_const]
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    obtain ⟨hp2, hpS⟩ := Finset.mem_erase.mp hp
    exact ((Finset.mem_filter.mp (hsub hpS)).2.1.even_sub_one hp2).two_dvd
  have hdiv : 2 ^ (S.erase 2).card ∣ n := htwo.trans
    ((Finset.prod_dvd_prod_of_subset (S.erase 2) S (fun p => p - 1) (Finset.erase_subset 2 S)).trans hprod)
  have herase := (Nat.prime_two.pow_dvd_iff_le_factorization hn.ne').mp hdiv
  have hcard : S.card ≤ (S.erase 2).card + 1 := by
    calc
      S.card ≤ (insert 2 (S.erase 2)).card := Finset.card_le_card (by
        intro p hp
        by_cases h : p = 2
        · simp [h]
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h, hp⟩))
      _ ≤ _ := Finset.card_insert_le _ _
  omega

lemma card_bounded_subset_family_le (F : Finset (Finset ℕ)) (P : Finset ℕ) (K : ℕ)
    (hF : ∀ S ∈ F, S ⊆ P ∧ S.card ≤ K) :
    F.card ≤ (K + 1) * (P.card + 1) ^ K := by
  classical
  have hsub : F ⊆ (Finset.range (K + 1)).biUnion (fun i => P.powersetCard i) := by
    intro S hS
    exact Finset.mem_biUnion.mpr ⟨S.card, Finset.mem_range.mpr (by have := (hF S hS).2; omega),
      Finset.mem_powersetCard.mpr ⟨(hF S hS).1, rfl⟩⟩
  calc
    F.card ≤ ((Finset.range (K + 1)).biUnion (fun i => P.powersetCard i)).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range (K + 1), (P.powersetCard i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range (K + 1), (P.card + 1) ^ K := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.card_powersetCard]
      exact (Nat.choose_le_pow _ _).trans
        ((Nat.pow_le_pow_left (Nat.le_succ P.card) _).trans
          (Nat.pow_le_pow_right (by omega) (by have := Finset.mem_range.mp hi; omega)))
    _ = _ := by simp

lemma shiftedPrimeDivisors_card_le_divisors_card {n : ℕ} (hn : 0 < n) :
    (shiftedPrimeDivisors n).card ≤ n.divisors.card := by
  apply Finset.card_le_card_of_injOn (fun p : ℕ => p - 1)
  · intro p hp
    change p ∈ shiftedPrimeDivisors n at hp
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hp).2.2, hn.ne'⟩
  · intro p hp q hq h
    change p ∈ shiftedPrimeDivisors n at hp
    change q ∈ shiftedPrimeDivisors n at hq
    have hp2 := (Finset.mem_filter.mp hp).2.1.two_le
    have hq2 := (Finset.mem_filter.mp hq).2.1.two_le
    change p - 1 = q - 1 at h
    omega

/-- Bounded 2-adic valuation restricts the number of possible supports and
bounds totient multiplicity by a fixed polynomial in the divisor count. -/
lemma g_le_divisor_polynomial_of_two_valuation_le (n K : ℕ) (hn : 0 < n)
    (hK : n.factorization 2 ≤ K) :
    g n ≤ (K + 2) * (n.divisors.card + 1) ^ (K + 1) := by
  rw [g_eq_card_admissibleSupports hn]
  calc
    (admissibleSupports n).card ≤ ((K + 1) + 1) * ((shiftedPrimeDivisors n).card + 1) ^ (K + 1) := by
      apply card_bounded_subset_family_le
      intro S hS
      refine ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1, ?_⟩
      exact (admissibleSupport_card_le_two_valuation hn hS).trans (Nat.add_le_add_right hK 1)
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.add_le_add_right (shiftedPrimeDivisors_card_le_divisors_card hn) 1) _)

/-- The divisor-counting function has uniform subpower growth. -/
lemma eventually_card_divisors_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n.divisors.card : ℝ) ≤ (n : ℝ) ^ ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
  have hkR : 0 < (k : ℝ) := (div_pos (by norm_num) hε).trans hk
  have hkN : 0 < k := by exact_mod_cast hkR
  have hkε : 2 < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hk
  filter_upwards [eventually_ge_atTop 1,
    eventually_ge_atTop ((k.factorial * 2 ^ k) ^ (2 ^ k))] with n hn hC
  have hpow : n.divisors.card ^ k ≤ n ^ 2 := by
    calc
      _ ≤ (k.factorial * 2 ^ k) ^ (2 ^ k) * n := card_divisors_pow_le n k (by omega)
      _ ≤ n * n := Nat.mul_le_mul_right _ hC
      _ = _ := (pow_two n).symm
  have hpowR : (n.divisors.card : ℝ) ^ k ≤ (n : ℝ) ^ (2 : ℕ) := by exact_mod_cast hpow
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbound : (n : ℝ) ^ (2 : ℕ) ≤ ((n : ℝ) ^ ε) ^ k := by
    rw [← Real.rpow_natCast (n : ℝ) 2,
      ← Real.rpow_natCast ((n : ℝ) ^ ε) k,
      ← Real.rpow_mul (Nat.cast_nonneg n)]
    apply Real.rpow_le_rpow_of_exponent_le hnR
    norm_num
    linarith
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg n.divisors.card)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) hkN.ne').mp (hpowR.trans hbound)

/-- For every fixed bound on the 2-adic valuation, the totient multiplicity
is eventually below every positive real power. -/
lemma eventually_g_le_rpow_of_two_valuation_le (K : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, n.factorization 2 ≤ K → (g n : ℝ) ≤ (n : ℝ) ^ δ := by
  let e : ℝ := δ / (2 * ((K : ℝ) + 1))
  have he : 0 < e := div_pos hδ (by positivity)
  let C : ℝ := ((K : ℝ) + 2) * 2 ^ (K + 1)
  have heq : e * ((K : ℝ) + 1) = δ / 2 := by
    dsimp [e]
    field_simp
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (δ / 2)) atTop atTop :=
    (tendsto_rpow_atTop (half_pos hδ)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_card_divisors_le_rpow e he,
    hlim.eventually (eventually_ge_atTop C), eventually_ge_atTop 1] with n hnD hnC hn hK
  have hnpos : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnRpos : (0 : ℝ) < n := by positivity
  have hge : (1 : ℝ) ≤ (n : ℝ) ^ e := Real.one_le_rpow hnR he.le
  have hgpoly : (g n : ℝ) ≤ ((K : ℝ) + 2) * ((n.divisors.card : ℝ) + 1) ^ (K + 1) := by
    exact_mod_cast g_le_divisor_polynomial_of_two_valuation_le n K hnpos hK
  have hpower : ((n : ℝ) ^ e) ^ (K + 1) = (n : ℝ) ^ (δ / 2) := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ e) (K + 1), ← Real.rpow_mul hnRpos.le]
    push_cast
    rw [heq]
  calc
    (g n : ℝ) ≤ ((K : ℝ) + 2) * ((n.divisors.card : ℝ) + 1) ^ (K + 1) := hgpoly
    _ ≤ ((K : ℝ) + 2) * (2 * (n : ℝ) ^ e) ^ (K + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    _ = C * (n : ℝ) ^ (δ / 2) := by rw [mul_pow, hpower]; dsimp [C]; ring
    _ ≤ (n : ℝ) ^ (δ / 2) * (n : ℝ) ^ (δ / 2) :=
      mul_le_mul_of_nonneg_right hnC (Real.rpow_nonneg hnRpos.le _)
    _ = (n : ℝ) ^ δ := by rw [← Real.rpow_add hnRpos]; congr 1; ring

lemma finite_g_gt_rpow_of_two_valuation_le (K : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    {n : ℕ | n.factorization 2 ≤ K ∧ (g n : ℝ) > (n : ℝ) ^ δ}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_g_le_rpow_of_two_valuation_le K δ hδ)
  apply (Set.finite_Iio N).subset
  intro n hn
  change n < N
  by_contra h
  exact (not_lt_of_ge (hN n (Nat.le_of_not_gt h) hn.1)) hn.2

/-- Squarefree output values cannot witness any fixed positive-power lower
bound infinitely often, even though their prime supports can be arbitrarily large. -/
lemma finite_g_gt_rpow_on_squarefree (δ : ℝ) (hδ : 0 < δ) :
    {n : ℕ | Squarefree n ∧ (g n : ℝ) > (n : ℝ) ^ δ}.Finite := by
  apply (finite_g_gt_rpow_of_two_valuation_le 1 δ hδ).subset
  intro n hn
  exact ⟨hn.1.natFactorization_le_one 2, hn.2⟩

/-- For any fixed positive exponent, all but finitely many witnesses must
be divisible by any prescribed power of two. -/
lemma finite_g_gt_rpow_not_dvd_two_pow (K : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    {n : ℕ | ¬2 ^ K ∣ n ∧ (g n : ℝ) > (n : ℝ) ^ δ}.Finite := by
  apply (finite_g_gt_rpow_of_two_valuation_le K δ hδ).subset
  intro n hn
  have hn0 : n ≠ 0 := by intro h; exact hn.1 (h ▸ dvd_zero _)
  have hK : ¬K ≤ n.factorization 2 := by
    intro h
    exact hn.1 ((Nat.prime_two.pow_dvd_iff_le_factorization hn0).mpr h)
  exact ⟨by omega, hn.2⟩

lemma infinite_g_gt_rpow_and_dvd_two_pow (K : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (H : {n : ℕ | (g n : ℝ) > (n : ℝ) ^ δ}.Infinite) :
    {n : ℕ | 2 ^ K ∣ n ∧ (g n : ℝ) > (n : ℝ) ^ δ}.Infinite := by
  apply (H.diff (finite_g_gt_rpow_not_dvd_two_pow K δ hδ)).mono
  intro n hn
  change (g n : ℝ) > (n : ℝ) ^ δ ∧
    ¬(¬2 ^ K ∣ n ∧ (g n : ℝ) > (n : ℝ) ^ δ) at hn
  exact ⟨by by_contra h; exact hn.2 ⟨h, hn.1⟩, hn.1⟩

#print axioms card_divisors_pow_le
#print axioms g_le_divisor_polynomial_of_two_valuation_le
#print axioms finite_g_gt_rpow_of_two_valuation_le
#print axioms finite_g_gt_rpow_on_squarefree
#print axioms infinite_g_gt_rpow_and_dvd_two_pow

end Erdos821
