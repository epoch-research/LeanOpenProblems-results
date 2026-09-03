import Submission.PrimeReciprocalEstimate

/-!
A refinement of the explicit Brun upper bound to truncation order `O(log log k)`.
This remains a partial result, not a proof of the quadratic conjecture.
-/
namespace Erdos970.BrunCriterion

/-- Exponential bounds for the sieve density and the tail generating function. -/
theorem prime_product_exp_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (Real.exp (-2 * ∑ p ∈ P, (1 : ℝ) / p) ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ))) ∧
    ((∏ p ∈ P, (1 + 2 * (1 / (p : ℝ)))) ≤ Real.exp (2 * ∑ p ∈ P, (1 : ℝ) / p)) := by
  classical
  have hfactor (p : ℕ) (hp : p ∈ P) : Real.exp (-2 * (1 / (p : ℝ))) ≤ 1 - 1 / (p : ℝ) := by
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hpRpos : 0 < (p : ℝ) := by linarith
    have hx0 : 0 ≤ 1 / (p : ℝ) := by positivity
    have hx1 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpR
    have hy : 0 < 1 - 1 / (p : ℝ) := by linarith
    have hpoly : 1 ≤ (1 + 2 * (1 / (p : ℝ))) * (1 - 1 / (p : ℝ)) := by
      nlinarith [mul_nonneg hx0 (show 0 ≤ 1 - 2 * (1 / (p : ℝ)) by linarith)]
    have hinv : (1 - 1 / (p : ℝ))⁻¹ ≤ 1 + 2 * (1 / (p : ℝ)) := by
      rw [inv_eq_one_div]
      exact (div_le_iff₀ hy).mpr hpoly
    have hl := Real.one_sub_inv_le_log_of_pos hy
    have hh : -2 * (1 / (p : ℝ)) ≤ Real.log (1 - 1 / (p : ℝ)) := by linarith
    simpa only [Real.exp_log hy] using Real.exp_le_exp.mpr hh
  constructor
  · rw [Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_le_prod (fun p hp => (Real.exp_pos _).le) hfactor
  · rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      positivity
    · intro p hp
      simpa only [add_comm] using Real.add_one_le_exp (2 * (1 / (p : ℝ)))

/-- The truncation order only needs to dominate the total reciprocal-prime mass. -/
theorem isJacobsthalBound_of_reciprocal_order (k t : ℕ) (ht : Odd t)
    (horder : ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      4 * (∑ p ∈ P, (1 : ℝ) / p) ≤ (t : ℝ) * Real.log 2) :
    IsJacobsthalBound k (4 * (k + 1) ^ (t + 1)) := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hPk, r, hcover⟩ :=
    (not_isJacobsthalBound_iff_cover k (4 * (k + 1) ^ (t + 1))).mp hbad
  let K : ℝ := (k : ℝ) + 1
  let S : ℝ := ∑ p ∈ P, (1 : ℝ) / p
  let D : ℝ := ∏ p ∈ P, (1 - 1 / (p : ℝ))
  let R : ℝ := ∏ p ∈ P, (1 + 2 * (1 / (p : ℝ)))
  have hK : 0 < K := by dsimp [K]; positivity
  have hPkR : (P.card : ℝ) + 1 ≤ K := by dsimp [K]; exact_mod_cast Nat.add_le_add_right hPk 1
  have hD : 1 / K ≤ D := (one_div_le_one_div_of_le (by positivity) hPkR).trans
    (prime_product_bounds P hP).1
  obtain ⟨hden, hgen⟩ := prime_product_exp_bounds P hP
  change Real.exp (-2 * S) ≤ D at hden
  change R ≤ Real.exp (2 * S) at hgen
  have hR : R ≤ (2 : ℝ) ^ t * D := by
    calc
      R ≤ Real.exp (2 * S) := hgen
      _ ≤ (2 : ℝ) ^ t * Real.exp (-2 * S) := by
        have heq : (2 : ℝ) ^ t = Real.exp ((t : ℝ) * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        rw [heq, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hh := horder P hP hPk
        change 4 * S ≤ _ at hh
        linarith
      _ ≤ (2 : ℝ) ^ t * D := mul_le_mul_of_nonneg_left hden (by positivity)
  have herr : R / (2 : ℝ) ^ (t + 1) ≤ D / 2 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    rw [pow_succ]
    nlinarith only [hR]
  have htail := trunc_value_lower P (fun p => 1 / (p : ℝ)) (fun p hp => by positivity) t
  have heq : (∑ Q ∈ truncSets P t, (-1 : ℝ) ^ Q.card * ∏ p ∈ Q, (1 / (p : ℝ))) =
      truncDensity P t := by
    simp only [truncDensity, div_eq_mul_inv, one_mul, Finset.prod_inv_distrib]
  rw [heq] at htail
  change D - R / (2 : ℝ) ^ (t + 1) ≤ truncDensity P t at htail
  have hinv : (1 / K) / 2 = 1 / (2 * K) := by rw [div_div, mul_comm K 2]
  have hdensity : 1 / (2 * K) ≤ truncDensity P t := by
    rw [← hinv]
    linarith
  have hc := cover_density_le P hP r (4 * (k + 1) ^ (t + 1)) t ht hcover
  have hcardR : ((truncSets P t).card : ℝ) ≤ K ^ t := by
    have hh : (truncSets P t).card ≤ (k + 1) ^ t :=
      (truncSets_card_le P t).trans (Nat.pow_le_pow_left (Nat.add_le_add_right hPk 1) t)
    dsimp [K]
    exact_mod_cast hh
  have hm : ((4 * (k + 1) ^ (t + 1) : ℕ) : ℝ) = 4 * K ^ (t + 1) := by
    dsimp only [K]
    push_cast
    rfl
  rw [hm] at hc
  have hl := mul_le_mul_of_nonneg_left hdensity (show 0 ≤ 4 * K ^ (t + 1) by positivity)
  have hcancel : 4 * K ^ (t + 1) * (1 / (2 * K)) = 2 * K ^ t := by
    rw [pow_succ]
    field_simp
    ring
  rw [hcancel] at hl
  have hpos : 0 < K ^ t := by positivity
  linarith

/-- An explicit upper bound with exponent of order `log log k`. -/
theorem isJacobsthalBound_refined (k : ℕ) :
    IsJacobsthalBound k
      (4 * (k + 1) ^ (16 * Nat.clog 2 (Nat.log 2 (k + 1) + 1) + 42)) := by
  let J := Nat.clog 2 (Nat.log 2 (k + 1) + 1)
  have hodd : Odd (16 * J + 41) := ⟨8 * J + 20, by omega⟩
  have horder : ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ k →
      4 * (∑ p ∈ P, (1 : ℝ) / p) ≤ ((16 * J + 41 : ℕ) : ℝ) * Real.log 2 := by
    intro P hP hPk
    have hh := prime_reciprocal_sum_le k P hP hPk
    change (∑ p ∈ P, (1 : ℝ) / p) ≤ 5 + 4 * (J : ℝ) * Real.log 2 at hh
    have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hl ⊢
      exact hl
    push_cast
    nlinarith only [hh, hlog]
  convert isJacobsthalBound_of_reciprocal_order k (16 * J + 41) hodd horder using 1

theorem jacobsthalFunction_le_refined (k : ℕ) :
    jacobsthalFunction k ≤
      4 * (k + 1) ^ (16 * Nat.clog 2 (Nat.log 2 (k + 1) + 1) + 42) :=
  (jacobsthalFunction_le_iff k _).mpr (isJacobsthalBound_refined k)

#print axioms prime_product_exp_bounds
#print axioms jacobsthalFunction_le_refined
end Erdos970.BrunCriterion
