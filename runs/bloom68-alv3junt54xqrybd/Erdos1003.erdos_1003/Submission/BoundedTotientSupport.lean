import Submission.EulerProductSupport

/-!
# Bounded prime support for adjacent totient coincidences

The proof uses finite Euler-product injectivity and a finite-cover induction.
All finiteness assertions concern solutions with a fixed bound on the number
of distinct prime factors of the two adjacent integers together.
-/

namespace BoundedTotientSupport
set_option maxHeartbeats 200000

open scoped BigOperators
open EulerProductSupport

/-- The elementary product estimate `1 - ∏ (1 - x) ≤ ∑ x`,
specialized to reciprocal primes. -/
theorem one_sub_eulerRatio_le_sum_inv {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) :
    1 - eulerRatio S ≤ ∑ p ∈ S, (p : ℚ)⁻¹ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have hpPrime := hS p (Finset.mem_insert_self p S)
    have hSPrime : ∀ q ∈ S, Nat.Prime q :=
      fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hprod := eulerRatio_le_one hSPrime
    have hinv : 0 ≤ (p : ℚ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
    have hmul := mul_le_mul_of_nonneg_left hprod hinv
    have hi := ih hSPrime
    simp only [eulerRatio, Finset.prod_insert hp, Finset.sum_insert hp] at *
    nlinarith

/-- Adding prime factors changes the Euler ratio by no more than the sum
of the reciprocals of the added primes. -/
theorem eulerRatio_tail_sum {A S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hAS : A ⊆ S) :
    |eulerRatio A - eulerRatio S| ≤ ∑ p ∈ S \ A, (p : ℚ)⁻¹ := by
  have hA : ∀ p ∈ A, Nat.Prime p := fun p hp => hS p (hAS hp)
  have hD : ∀ p ∈ S \ A, Nat.Prime p :=
    fun p hp => hS p (Finset.mem_sdiff.mp hp).1
  have hA0 := (eulerRatio_pos hA).le
  have hA1 := eulerRatio_le_one hA
  have hD1 := eulerRatio_le_one hD
  have hsum := one_sub_eulerRatio_le_sum_inv hD
  have hfactor : eulerRatio S = eulerRatio A * eulerRatio (S \ A) := by
    rw [← eulerRatio_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hAS]
  have hnonneg : 0 ≤ eulerRatio A - eulerRatio S := by
    rw [hfactor]
    nlinarith
  rw [abs_of_nonneg hnonneg, hfactor]
  have hmul := mul_le_mul_of_nonneg_right hA1 (sub_nonneg.mpr hD1)
  nlinarith

/-- If every newly added prime exceeds `L`, the tail error is at most
`S.card / (L+1)`. -/
theorem eulerRatio_tail_bound {A S : Finset ℕ} (L : ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (hAS : A ⊆ S)
    (hlarge : ∀ p ∈ S \ A, L < p) :
    |eulerRatio A - eulerRatio S| ≤ (S.card : ℚ) / (L + 1 : ℚ) := by
  have hL : (0 : ℚ) < L + 1 := by positivity
  calc
    |eulerRatio A - eulerRatio S|
        ≤ ∑ p ∈ S \ A, (p : ℚ)⁻¹ := eulerRatio_tail_sum hS hAS
    _ ≤ ∑ _p ∈ S \ A, (1 / (L + 1 : ℚ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hLp : (L + 1 : ℚ) ≤ p := by exact_mod_cast (hlarge p hp)
      simpa only [one_div] using one_div_le_one_div_of_le hL hLp
    _ = ((S \ A).card : ℚ) / (L + 1 : ℚ) := by
      simp [div_eq_mul_inv]
    _ ≤ (S.card : ℚ) / (L + 1 : ℚ) := by
      apply div_le_div_of_nonneg_right _ hL.le
      exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : S \ A ⊆ S)

/-- Equal adjacent totients force the corresponding Euler ratios to be
within `1/(n+1)` of one another. -/
theorem adjacent_eulerRatio_gap {n : ℕ}
    (h : n.totient = (n + 1).totient) :
    |eulerRatio n.primeFactors - eulerRatio (n + 1).primeFactors| ≤
      1 / (n + 1 : ℚ) := by
  have hn1 : (0 : ℚ) < n + 1 := by positivity
  have heq : (n : ℚ) * eulerRatio n.primeFactors =
      (n + 1 : ℚ) * eulerRatio (n + 1).primeFactors := by
    simpa only [eulerRatio, Nat.cast_add, Nat.cast_one,
      Nat.totient_eq_mul_prod_factors] using congrArg (fun a : ℕ => (a : ℚ)) h
  have hdiff : eulerRatio n.primeFactors - eulerRatio (n + 1).primeFactors =
      eulerRatio n.primeFactors / (n + 1 : ℚ) := by
    apply (eq_div_iff hn1.ne').mpr
    nlinarith [heq]
  rw [hdiff, abs_of_nonneg (div_nonneg
    (eulerRatio_pos (fun p hp => Nat.prime_of_mem_primeFactors hp)).le hn1.le)]
  exact div_le_div_of_nonneg_right
    (eulerRatio_le_one (fun p hp => Nat.prime_of_mem_primeFactors hp)) hn1.le

/-- For unequal fixed Euler ratios and bounded full support, any sufficiently
large solution must introduce a new prime below a fixed cutoff. -/
theorem exists_small_new_prime_cutoff (A B : Finset ℕ) (M : ℕ)
    (hneq : eulerRatio A ≠ eulerRatio B) :
    ∃ L : ℕ, ∀ n : ℕ,
      n.totient = (n + 1).totient →
      A ⊆ n.primeFactors → B ⊆ (n + 1).primeFactors →
      n.primeFactors.card + (n + 1).primeFactors.card ≤ M →
      n ≤ L ∨ ∃ p ≤ L,
        (p ∈ n.primeFactors ∧ p ∉ A) ∨
        (p ∈ (n + 1).primeFactors ∧ p ∉ B) := by
  have hδ : 0 < |eulerRatio A - eulerRatio B| := abs_pos.mpr (sub_ne_zero.mpr hneq)
  have hM : (0 : ℚ) < 2 * M + 1 := by positivity
  obtain ⟨L, hL⟩ := exists_nat_one_div_lt (div_pos hδ hM)
  refine ⟨L, ?_⟩
  intro n htot hA hB hcard
  by_cases hn : n ≤ L
  · exact Or.inl hn
  right
  by_contra hsmall
  have hlargeA : ∀ p ∈ n.primeFactors \ A, L < p := by
    intro p hp
    by_contra hnot
    exact hsmall ⟨p, le_of_not_gt hnot, Or.inl (Finset.mem_sdiff.mp hp)⟩
  have hlargeB : ∀ p ∈ (n + 1).primeFactors \ B, L < p := by
    intro p hp
    by_contra hnot
    exact hsmall ⟨p, le_of_not_gt hnot, Or.inr (Finset.mem_sdiff.mp hp)⟩
  have hden : (0 : ℚ) < L + 1 := by positivity
  have hcardA : (n.primeFactors.card : ℚ) ≤ M := by
    exact_mod_cast (show n.primeFactors.card ≤ M by omega)
  have hcardB : ((n + 1).primeFactors.card : ℚ) ≤ M := by
    exact_mod_cast (show (n + 1).primeFactors.card ≤ M by omega)
  have htailA : |eulerRatio A - eulerRatio n.primeFactors| ≤
      (M : ℚ) / (L + 1 : ℚ) :=
    (eulerRatio_tail_bound L (fun p hp => Nat.prime_of_mem_primeFactors hp) hA hlargeA).trans
      (div_le_div_of_nonneg_right hcardA hden.le)
  have htailB : |eulerRatio B - eulerRatio (n + 1).primeFactors| ≤
      (M : ℚ) / (L + 1 : ℚ) :=
    (eulerRatio_tail_bound L (fun p hp => Nat.prime_of_mem_primeFactors hp) hB hlargeB).trans
      (div_le_div_of_nonneg_right hcardB hden.le)
  have hgap : |eulerRatio n.primeFactors - eulerRatio (n + 1).primeFactors| ≤
      1 / (L + 1 : ℚ) := by
    apply (adjacent_eulerRatio_gap htot).trans
    apply one_div_le_one_div_of_le hden
    exact_mod_cast (show L + 1 ≤ n + 1 by omega)
  have htriangle : |eulerRatio A - eulerRatio B| ≤
      |eulerRatio A - eulerRatio n.primeFactors| +
      |eulerRatio n.primeFactors - eulerRatio (n + 1).primeFactors| +
      |eulerRatio B - eulerRatio (n + 1).primeFactors| := by
    have h1 := abs_sub_le (eulerRatio A) (eulerRatio n.primeFactors) (eulerRatio B)
    have h2 := abs_sub_le (eulerRatio n.primeFactors)
      (eulerRatio (n + 1).primeFactors) (eulerRatio B)
    rw [abs_sub_comm (eulerRatio (n + 1).primeFactors) (eulerRatio B)] at h2
    linarith only [h1, h2]
  have hbound : |eulerRatio A - eulerRatio B| ≤
      (2 * M + 1 : ℚ) / (L + 1 : ℚ) := by
    calc
      _ ≤ (M : ℚ) / (L + 1 : ℚ) + 1 / (L + 1 : ℚ) +
          (M : ℚ) / (L + 1 : ℚ) := htriangle.trans (by linarith only [htailA, hgap, htailB])
      _ = _ := by ring
  have hstrict : (2 * M + 1 : ℚ) / (L + 1 : ℚ) <
      |eulerRatio A - eulerRatio B| := by
    have := (mul_lt_mul_of_pos_left hL hM)
    rw [mul_div_cancel₀ _ hM.ne'] at this
    simpa only [mul_one_div] using this
  exact (not_lt_of_ge hbound) hstrict

/-- The prime supports of consecutive integers are disjoint. -/
theorem adjacent_primeFactors_disjoint (n : ℕ) :
    Disjoint n.primeFactors (n + 1).primeFactors := by
  apply Nat.Coprime.disjoint_primeFactors
  simp

/-- Solutions containing the fixed supports `A` and `B`, with at most `k`
additional prime factors in total. -/
def fixedSupportSolutions (A B : Finset ℕ) (k : ℕ) : Set ℕ :=
  {n | n.totient = (n + 1).totient ∧
    A ⊆ n.primeFactors ∧ B ⊆ (n + 1).primeFactors ∧
    n.primeFactors.card + (n + 1).primeFactors.card ≤ A.card + B.card + k}

/-- Fixing any nonempty pair of disjoint prime supports makes the family
with bounded additional support finite. -/
theorem finite_fixedSupportSolutions (k : ℕ) (A B : Finset ℕ)
    (hA : ∀ p ∈ A, Nat.Prime p) (hB : ∀ p ∈ B, Nat.Prime p)
    (hAB : Disjoint A B) (hne : (A ∪ B).Nonempty) :
    (fixedSupportSolutions A B k).Finite := by
  classical
  induction k generalizing A B with
  | zero =>
    obtain ⟨L, hL⟩ := exists_small_new_prime_cutoff A B (A.card + B.card)
      (eulerRatio_ne_of_disjoint hA hB hAB hne)
    apply (Set.finite_le_nat L).subset
    intro n hn
    rcases hn with ⟨htot, hAS, hBS, hcard⟩
    simp only [Nat.add_zero] at hcard
    rcases hL n htot hAS hBS hcard with hbound | ⟨p, _hpL, hnew⟩
    · exact hbound
    · rcases hnew with ⟨hpS, hpA⟩ | ⟨hpT, hpB⟩
      · have ha := Finset.card_le_card (Finset.insert_subset hpS hAS)
        rw [Finset.card_insert_of_notMem hpA] at ha
        have hb := Finset.card_le_card hBS
        omega
      · have ha := Finset.card_le_card hAS
        have hb := Finset.card_le_card (Finset.insert_subset hpT hBS)
        rw [Finset.card_insert_of_notMem hpB] at hb
        omega
  | succ k ih =>
    obtain ⟨L, hL⟩ := exists_small_new_prime_cutoff A B (A.card + B.card + (k + 1))
      (eulerRatio_ne_of_disjoint hA hB hAB hne)
    let P : Set ℕ := {p | p ≤ L ∧ Nat.Prime p ∧ p ∉ A ∧ p ∉ B}
    have hP : P.Finite := (Set.finite_le_nat L).subset fun p hp => hp.1
    have hleft : (⋃ p ∈ P, fixedSupportSolutions (insert p A) B k).Finite := by
      apply hP.biUnion
      intro p hp
      rcases hp with ⟨_hpL, hpPrime, _hpA, hpB⟩
      apply ih (insert p A) B
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hpPrime
        · exact hA q hq
      · exact hB
      · exact Finset.disjoint_insert_left.mpr ⟨hpB, hAB⟩
      · rcases hne with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        rcases Finset.mem_union.mp hq with hq | hq
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_insert_of_mem hq))
        · exact Finset.mem_union.mpr (Or.inr hq)
    have hright : (⋃ p ∈ P, fixedSupportSolutions A (insert p B) k).Finite := by
      apply hP.biUnion
      intro p hp
      rcases hp with ⟨_hpL, hpPrime, hpA, _hpB⟩
      apply ih A (insert p B)
      · exact hA
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hpPrime
        · exact hB q hq
      · exact Finset.disjoint_insert_right.mpr ⟨hpA, hAB⟩
      · rcases hne with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        rcases Finset.mem_union.mp hq with hq | hq
        · exact Finset.mem_union.mpr (Or.inl hq)
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_insert_of_mem hq))
    apply ((Set.finite_le_nat L).union (hleft.union hright)).subset
    intro n hn
    rcases hn with ⟨htot, hAS, hBS, hcard⟩
    rcases hL n htot hAS hBS hcard with hbound | ⟨p, hpL, hnew⟩
    · exact Or.inl hbound
    · have hdisj := adjacent_primeFactors_disjoint n
      rcases hnew with ⟨hpS, hpA⟩ | ⟨hpT, hpB⟩
      · have hpB : p ∉ B := fun hpB =>
          Finset.disjoint_left.mp hdisj hpS (hBS hpB)
        have hpP : p ∈ P := ⟨hpL, Nat.prime_of_mem_primeFactors hpS, hpA, hpB⟩
        refine Or.inr (Or.inl (Set.mem_iUnion₂.mpr ⟨p, hpP, ?_⟩))
        refine ⟨htot, Finset.insert_subset hpS hAS, hBS, ?_⟩
        rw [Finset.card_insert_of_notMem hpA]
        omega
      · have hpA : p ∉ A := fun hpA =>
          Finset.disjoint_left.mp hdisj (hAS hpA) hpT
        have hpP : p ∈ P := ⟨hpL, Nat.prime_of_mem_primeFactors hpT, hpA, hpB⟩
        refine Or.inr (Or.inr (Set.mem_iUnion₂.mpr ⟨p, hpP, ?_⟩))
        refine ⟨htot, hAS, Finset.insert_subset hpT hBS, ?_⟩
        rw [Finset.card_insert_of_notMem hpB]
        omega

/-- There are only finitely many adjacent totient coincidences whose combined
prime support has cardinality at most a prescribed natural number. -/
theorem finite_bounded_totient_support (K : ℕ) :
    Set.Finite {n : ℕ | n.totient = (n + 1).totient ∧
      (n.primeFactors ∪ (n + 1).primeFactors).card ≤ K} := by
  have htwo : ∀ p ∈ ({2} : Finset ℕ), Nat.Prime p := by simp [Nat.prime_two]
  have hempty : ∀ p ∈ (∅ : Finset ℕ), Nat.Prime p := by simp
  have hleft := finite_fixedSupportSolutions K {2} ∅ htwo hempty (by simp) (by simp)
  have hright := finite_fixedSupportSolutions K ∅ {2} hempty htwo (by simp) (by simp)
  apply (hleft.union hright).subset
  intro n hn
  rcases hn with ⟨htot, hcard⟩
  have hn0 : n ≠ 0 := by
    intro hn0
    subst n
    norm_num at htot
  have hsum : n.primeFactors.card + (n + 1).primeFactors.card ≤ K := by
    simpa only [Finset.card_union_of_disjoint (adjacent_primeFactors_disjoint n)] using hcard
  by_cases heven : Even n
  · left
    refine ⟨htot, ?_, Finset.empty_subset _, ?_⟩
    · exact Finset.singleton_subset_iff.mpr
        (Nat.prime_two.mem_primeFactors (even_iff_two_dvd.mp heven) hn0)
    · simp only [Finset.card_singleton, Finset.card_empty]
      omega
  · right
    refine ⟨htot, Finset.empty_subset _, ?_, ?_⟩
    · exact Finset.singleton_subset_iff.mpr
        (Nat.prime_two.mem_primeFactors (even_iff_two_dvd.mp (Nat.even_add_one.mpr heven))
          (Nat.succ_ne_zero n))
    · simp only [Finset.card_singleton, Finset.card_empty]
      omega


end BoundedTotientSupport
