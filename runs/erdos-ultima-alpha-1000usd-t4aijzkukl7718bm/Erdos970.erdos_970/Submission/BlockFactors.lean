import Submission.SievePolynomial

/-!
Pointwise and mean estimates for the upper and error factors in a block sieve.
-/
namespace Erdos970.BlockSieve.SievePolynomial

open Erdos970.BrunCriterion

noncomputable def badPrimes (P : Finset ℕ) (r : ℕ → ℕ) (i : ℕ) : Finset ℕ :=
  P.filter (fun p => i ≡ r p [MOD p])

theorem value_upper_eq (P : Finset ℕ) (r : ℕ → ℕ) (i t : ℕ) :
    (upper P t).value r i =
      ∑ Q ∈ truncSets (badPrimes P r i) t, (-1 : ℝ) ^ Q.card := by
  classical
  have hcoe : (upper P t).value r i = ∑ Q ∈ truncSets P t,
      (-1 : ℝ) ^ Q.card * (if ∀ p ∈ Q, i ≡ r p [MOD p] then 1 else 0) :=
    by
      simpa only [upper, value] using (Finset.sum_coe_sort (truncSets P t)
        (fun Q => (-1 : ℝ) ^ Q.card * (if ∀ p ∈ Q, i ≡ r p [MOD p] then 1 else 0)))
  rw [hcoe]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext Q
  simp only [truncSets, badPrimes, Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff]
  aesop

theorem value_errorTerm_eq (P : Finset ℕ) (r : ℕ → ℕ) (i t : ℕ) :
    (errorTerm P t).value r i = ((badPrimes P r i).card.choose (t + 1) : ℝ) := by
  classical
  have hcoe : (errorTerm P t).value r i = ∑ Q ∈ P.powersetCard (t + 1),
      (1 : ℝ) * (if ∀ p ∈ Q, i ≡ r p [MOD p] then 1 else 0) :=
    by
      simpa only [errorTerm, value] using (Finset.sum_coe_sort (P.powersetCard (t + 1))
        (fun Q => (1 : ℝ) * (if ∀ p ∈ Q, i ≡ r p [MOD p] then 1 else 0)))
  rw [hcoe]
  simp only [one_mul]
  rw [← Finset.sum_filter]
  have heq : (P.powersetCard (t + 1)).filter (fun Q => ∀ p ∈ Q, i ≡ r p [MOD p]) =
      (badPrimes P r i).powersetCard (t + 1) := by
    ext Q
    simp only [badPrimes, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_iff]
    aesop
  rw [heq]
  simp

theorem value_upper_formula (P : Finset ℕ) (r : ℕ → ℕ) (i t : ℕ) :
    (upper P t).value r i =
      ∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ j * ((badPrimes P r i).card.choose j : ℝ) := by
  rw [value_upper_eq]
  exact_mod_cast signed_trunc_eq (badPrimes P r i) t

/-- Even truncations are pointwise nonnegative; if a block hits, its error factor dominates it. -/
theorem value_factor_bounds (P : Finset ℕ) (r : ℕ → ℕ) (i t : ℕ) (ht : Even t) :
    0 ≤ (upper P t).value r i ∧ 0 ≤ (errorTerm P t).value r i ∧
      ((∃ p ∈ P, i ≡ r p [MOD p]) → (upper P t).value r i ≤ (errorTerm P t).value r i) := by
  classical
  rw [value_upper_formula, value_errorTerm_eq]
  cases hc : (badPrimes P r i).card with
  | zero =>
    have hbad : ¬∃ p ∈ P, i ≡ r p [MOD p] := by
      rintro ⟨p, hp, hip⟩
      have hh : (badPrimes P r i).Nonempty := ⟨p, Finset.mem_filter.mpr ⟨hp, hip⟩⟩
      have := Finset.card_pos.mpr hh
      omega
    have heq : (∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ j * (Nat.choose 0 j : ℝ)) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j hj hj0
        rw [Nat.choose_eq_zero_of_lt (by omega : 0 < j)]
        simp
      · simp
    simp [heq, Nat.choose_zero_succ, hbad]
  | succ n =>
    have heq : (∑ j ∈ Finset.range (t + 1), (-1 : ℝ) ^ j * (Nat.choose (n + 1) j : ℝ)) =
        (-1 : ℝ) ^ t * (n.choose t : ℝ) := by
      exact_mod_cast (Int.alternating_sum_range_choose_eq_choose (n := n) (m := t))
    rw [heq, ht.neg_one_pow, one_mul]
    refine ⟨by positivity, by positivity, fun _ => ?_⟩
    exact_mod_cast (show n.choose t ≤ (n + 1).choose (t + 1) by
      rw [Nat.choose_succ_succ]
      omega)

/-- The degree-`t+1` error is bounded by the same generating function as the discarded tail. -/
theorem mean_errorTerm_le (P : Finset ℕ) (t : ℕ) :
    (errorTerm P t).mean ≤ (∏ p ∈ P, (1 + 2 * (1 / (p : ℝ)))) / (2 : ℝ) ^ (t + 1) := by
  classical
  have heq : (errorTerm P t).mean = ∑ Q ∈ P.powersetCard (t + 1), ∏ p ∈ Q, (1 / (p : ℝ)) := by
    have hcoe : (errorTerm P t).mean = ∑ Q ∈ P.powersetCard (t + 1), (1 : ℝ) / ∏ p ∈ Q, (p : ℝ) :=
      Finset.sum_coe_sort (P.powersetCard (t + 1)) (fun Q => (1 : ℝ) / ∏ p ∈ Q, (p : ℝ))
    rw [hcoe]
    simp only [div_eq_mul_inv, one_mul, Finset.prod_inv_distrib]
  rw [heq]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (t + 1))).mpr
  rw [Finset.sum_mul, Finset.prod_one_add]
  have heq' : (∑ Q ∈ P.powersetCard (t + 1), (∏ p ∈ Q, (1 / (p : ℝ))) * 2 ^ (t + 1)) =
      ∑ Q ∈ P.powersetCard (t + 1), ∏ p ∈ Q, 2 * (1 / (p : ℝ)) := by
    apply Finset.sum_congr rfl
    intro Q hQ
    rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hQ).2, mul_comm]
  rw [heq']
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro Q hQ
    exact Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hQ).1
  · intro Q hQ _
    positivity

/-- Bounded reciprocal mass permits geometrically decreasing relative errors. -/
theorem block_mean_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℕ)
    (hmass : (∑ p ∈ P, (1 : ℝ) / p) ≤ 4) :
    let D := ∏ p ∈ P, (1 - 1 / (p : ℝ))
    D / 2 ≤ (upper P (2 * (n + 18))).mean ∧
      (errorTerm P (2 * (n + 18))).mean ≤ D / (2 : ℝ) ^ (n + 3) := by
  classical
  let D := ∏ p ∈ P, (1 - 1 / (p : ℝ))
  let R := ∏ p ∈ P, (1 + 2 * (1 / (p : ℝ)))
  let S := ∑ p ∈ P, (1 : ℝ) / p
  obtain ⟨hDexp, hRexp⟩ := prime_product_exp_bounds P hP
  change Real.exp (-2 * S) ≤ D at hDexp
  change R ≤ Real.exp (2 * S) at hRexp
  have hD : 0 < D := (Real.exp_pos _).trans_le hDexp
  have hR : R ≤ (2 : ℝ) ^ 32 * D := by
    have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hl ⊢
      exact hl
    calc
      R ≤ Real.exp (2 * S) := hRexp
      _ ≤ (2 : ℝ) ^ 32 * Real.exp (-2 * S) := by
        have heq : (2 : ℝ) ^ 32 = Real.exp (32 * Real.log 2) := by
          rw [show (32 : ℝ) = (32 : ℕ) by norm_num, Real.exp_nat_mul,
            Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        rw [heq, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        change S ≤ 4 at hmass
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hDexp (by positivity)
  have hpower : (2 : ℝ) ^ 32 * 2 ^ (n + 3) ≤ 2 ^ (2 * (n + 18) + 1) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have herr : R / (2 : ℝ) ^ (2 * (n + 18) + 1) ≤ D / 2 ^ (n + 3) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hR (by positivity : (0 : ℝ) ≤ 2 ^ (n + 3))
    have hh' := mul_le_mul_of_nonneg_left hpower hD.le
    nlinarith only [hh, hh']
  have herrhalf : D / (2 : ℝ) ^ (n + 3) ≤ D / 2 := by
    apply div_le_div_of_nonneg_left hD.le (by norm_num)
    have hh : (2 : ℝ) ^ 1 ≤ 2 ^ (n + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    simpa only [pow_one] using hh
  have hlow := trunc_value_lower P (fun p => (1 : ℝ) / p) (fun p hp => by positivity) (2 * (n + 18))
  have heq : (∑ Q ∈ truncSets P (2 * (n + 18)), (-1 : ℝ) ^ Q.card * ∏ p ∈ Q, (1 / (p : ℝ))) =
      (upper P (2 * (n + 18))).mean := by
    rw [mean_upper]
    simp only [truncDensity, div_eq_mul_inv, one_mul, Finset.prod_inv_distrib]
  rw [heq] at hlow
  change D - R / _ ≤ _ at hlow
  refine ⟨?_, (mean_errorTerm_le P _).trans herr⟩
  change D / 2 ≤ _
  linarith

theorem factor_cost_bounds (P : Finset ℕ) (t : ℕ) :
    (upper P t).cost ≤ ((P.card + 1 : ℕ) : ℝ) ^ (t + 1) ∧
    (errorTerm P t).cost ≤ ((P.card + 1 : ℕ) : ℝ) ^ (t + 1) := by
  constructor
  · rw [cost_upper]
    exact_mod_cast (truncSets_card_le P t).trans (Nat.pow_le_pow_right (by omega) (by omega : t ≤ t + 1))
  · rw [cost_errorTerm]
    exact_mod_cast (Nat.choose_le_pow P.card (t + 1)).trans (Nat.pow_le_pow_left (Nat.le_succ P.card) (t + 1))

#print axioms value_factor_bounds
#print axioms block_mean_bounds
end Erdos970.BlockSieve.SievePolynomial
