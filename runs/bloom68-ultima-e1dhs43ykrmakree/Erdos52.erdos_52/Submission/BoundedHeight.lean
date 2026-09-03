import Mathlib

/-!
# A product-set lower bound under a height restriction

This file proves a bounded-height partial result, not the unrestricted
sum-product conjecture. For every `η > 0` there is a constant `c > 0`,
independent of the finite set `A` and its height `H`, such that a set of
positive natural numbers bounded by `H ≥ 1` satisfies

`c * |A|² / H^η ≤ |A * A|`.

The arithmetic input is the ordinary bound `τ(n) ≤ Cδ * n^δ` for every
`δ > 0`. We prove it here from the divisor-count product formula, separating
the finitely many small primes from the large primes. No conjectural
sum-product estimate or result from `Submission.Spec` is used.

As a corollary, for fixed `K > 0` and `ε > 0`, nonempty sets with
`max A ≤ |A|^K` satisfy `c(K, ε) * |A|^(2 - ε) ≤ |A * A|`.
The dependence on the fixed height exponent `K` is essential to the
statement; this is not a uniform result for arbitrary heights.
-/

open scoped BigOperators Pointwise

namespace Erdos52.BoundedHeight

/-- A uniform bound for a linear function by a geometric progression.
The constant is at least one, which will allow us to enlarge a finite
set of exceptional primes. -/
lemma exists_linear_le_const_mul_pow {r : ℝ} (hr : 1 < r) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k : ℕ, (k : ℝ) + 1 ≤ B * r ^ k := by
  let B : ℝ := 1 + (r - 1)⁻¹
  have hr0 : 0 < r - 1 := sub_pos.mpr hr
  refine ⟨B, ?_, ?_⟩
  · dsimp [B]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hr0.le)
  · intro k
    have hBern : 1 + (k : ℝ) * (r - 1) ≤ r ^ k :=
      one_add_mul_sub_le_pow (by linarith) k
    have hk : (k : ℝ) ≤ (r - 1)⁻¹ * r ^ k := by
      rw [inv_mul_eq_div, le_div_iff₀ hr0]
      linarith
    have hpow : (1 : ℝ) ≤ r ^ k := one_le_pow₀ hr.le
    dsimp [B]
    nlinarith

/-- Beyond a fixed natural threshold, `p^δ ≥ 2`. -/
lemma exists_rpow_threshold {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℕ, ∀ p : ℕ, T ≤ p → (2 : ℝ) ≤ (p : ℝ) ^ δ := by
  obtain ⟨T, hT⟩ := exists_nat_ge ((2 : ℝ) ^ (1 / δ))
  refine ⟨T, fun p hp => ?_⟩
  have hbase : (2 : ℝ) ^ (1 / δ) ≤ (p : ℝ) :=
    hT.trans (by exact_mod_cast hp)
  have h := Real.rpow_le_rpow (by positivity) hbase hδ.le
  simpa only [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    one_div_mul_cancel hδ.ne', Real.rpow_one] using h

/-- The usual subpolynomial upper bound for the number of positive divisors.
The constant is uniform in every positive integer `n`. -/
theorem exists_divisors_card_le_rpow (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ δ := by
  obtain ⟨B, hB, hlinear⟩ :=
    exists_linear_le_const_mul_pow (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hδ)
  obtain ⟨T, hT⟩ := exists_rpow_threshold hδ
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  refine ⟨B ^ T, pow_pos hBpos T, fun n hn => ?_⟩
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) :
      ((n.factorization p : ℕ) : ℝ) + 1 ≤
        (if p < T then B else 1) * ((p : ℝ) ^ (n.factorization p)) ^ δ := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hsmall : p < T
    · rw [if_pos hsmall, ← Real.rpow_pow_comm (by positivity)]
      exact (hlinear (n.factorization p)).trans
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hp2 hδ.le) _)
          hBpos.le)
    · rw [if_neg hsmall, one_mul, ← Real.rpow_pow_comm (by positivity)]
      have htwo : ((n.factorization p : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (n.factorization p) := by
        simpa only [show (2 : ℝ) - 1 = 1 by norm_num, mul_one, add_comm] using
          one_add_mul_sub_le_pow (by norm_num : (-1 : ℝ) ≤ 2) (n.factorization p)
      exact htwo.trans (pow_le_pow_left₀ (by norm_num) (hT p (Nat.le_of_not_gt hsmall)) _)
  have hsmallcard : (n.primeFactors.filter fun p => p < T).card ≤ T := by
    calc
      _ ≤ (Finset.range T).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = T := Finset.card_range T
  have hconst : (∏ p ∈ n.primeFactors, if p < T then B else 1) ≤ B ^ T := by
    rw [← Finset.prod_filter, Finset.prod_const]
    exact pow_le_pow_right₀ hB hsmallcard
  have hprod : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) ^ δ) =
      (n : ℝ) ^ δ := by
    rw [Real.finset_prod_rpow _ _ (by intros; positivity)]
    congr 1
    exact_mod_cast (Nat.factorization_prod_pow_eq_self hn.ne')
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, (((n.factorization p : ℕ) : ℝ) + 1) := by
      rw [Nat.card_divisors hn.ne']
      push_cast
      rfl
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < T then B else 1) * ((p : ℝ) ^ (n.factorization p)) ^ δ :=
      Finset.prod_le_prod (by intros; positivity) hfactor
    _ = (∏ p ∈ n.primeFactors, if p < T then B else 1) * (n : ℝ) ^ δ := by
      rw [Finset.prod_mul_distrib, hprod]
    _ ≤ B ^ T * (n : ℝ) ^ δ := mul_le_mul_of_nonneg_right hconst (by positivity)

/-- For a positive product, projecting an ordered factorization to its first
factor injects the product fiber into the positive divisors of the product.
No positivity restriction on the ambient finite set of pairs is needed. -/
lemma product_fiber_card_le_divisors_card (S : Finset (ℕ × ℕ))
    (n : ℕ) (hn : 0 < n) :
    (S.filter fun ab => ab.1 * ab.2 = n).card ≤ n.divisors.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro ab hab
    have habmul := (Finset.mem_filter.mp hab).2
    exact Nat.mem_divisors.mpr ⟨⟨ab.2, habmul.symm⟩, hn.ne'⟩
  · intro x hx y hy hxy
    have hxmul := (Finset.mem_filter.mp hx).2
    have hymul := (Finset.mem_filter.mp hy).2
    apply Prod.ext hxy
    have hxpos : 0 < x.1 := Nat.pos_of_mul_pos_right (hxmul.symm ▸ hn)
    apply Nat.mul_left_cancel hxpos
    calc
      x.1 * x.2 = n := hxmul
      _ = y.1 * y.2 := hymul.symm
      _ = x.1 * y.2 := by rw [hxy]

/-- A real-valued uniform bound on the fibers gives the usual image-cardinality
inequality, with no rounding of the fiber bound. -/
lemma card_le_card_image_mul_of_fiber_bound {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) (D : ℝ)
    (hD : ∀ b ∈ S.image f, ((S.filter fun a => f a = b).card : ℝ) ≤ D) :
    (S.card : ℝ) ≤ ((S.image f).card : ℝ) * D := by
  calc
    (S.card : ℝ) = ∑ b ∈ S.image f, ((S.filter fun a => f a = b).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image f S
    _ ≤ ∑ _b ∈ S.image f, D := Finset.sum_le_sum hD
    _ = ((S.image f).card : ℝ) * D := by simp

/-- Bounded-height product-set estimate, allowing a real height bound.
The constant depends only on `η`, not on `A` or `H`. The empty set is allowed. -/
theorem exists_product_card_lower_bound_of_real_height (η : ℝ) (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ ∀ (A : Finset ℕ) (H : ℝ), 1 ≤ H →
      (∀ a ∈ A, 0 < a) → (∀ a ∈ A, (a : ℝ) ≤ H) →
      c * (A.card : ℝ) ^ 2 / H ^ η ≤ ((A * A).card : ℝ) := by
  obtain ⟨C, hC, hdiv⟩ := exists_divisors_card_le_rpow (η / 2) (by linarith)
  refine ⟨C⁻¹, inv_pos.mpr hC, fun A H hH hpos hheight => ?_⟩
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hHpow : 0 < H ^ η := Real.rpow_pos_of_pos hHpos η
  have hfib : ∀ p ∈ (A ×ˢ A).image (fun ab => ab.1 * ab.2),
      (((A ×ˢ A).filter fun ab => ab.1 * ab.2 = p).card : ℝ) ≤ C * H ^ η := by
    intro p hp
    rw [Finset.image_mul_product] at hp
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_mul.mp hp
    have habpos : 0 < a * b := Nat.mul_pos (hpos a ha) (hpos b hb)
    have habheight : ((a * b : ℕ) : ℝ) ≤ H ^ 2 := by
      push_cast
      simpa only [pow_two] using
        mul_le_mul (hheight a ha) (hheight b hb) (by positivity) hHpos.le
    have habpow : ((a * b : ℕ) : ℝ) ^ (η / 2) ≤ H ^ η := by
      calc
        _ ≤ (H ^ (2 : ℕ)) ^ (η / 2) :=
          Real.rpow_le_rpow (by positivity) habheight (by linarith)
        _ = H ^ η := by
          rw [← Real.rpow_natCast_mul hHpos.le]
          congr 1
          push_cast
          ring
    calc
      _ ≤ ((a * b).divisors.card : ℝ) := by
        exact_mod_cast product_fiber_card_le_divisors_card (A ×ˢ A) (a * b) habpos
      _ ≤ C * ((a * b : ℕ) : ℝ) ^ (η / 2) := hdiv (a * b) habpos
      _ ≤ C * H ^ η := mul_le_mul_of_nonneg_left habpow hC.le
  have hcount : (A.card : ℝ) ^ 2 ≤ ((A * A).card : ℝ) * (C * H ^ η) := by
    simpa only [Finset.card_product, Nat.cast_mul, pow_two, Finset.image_mul_product] using
      card_le_card_image_mul_of_fiber_bound (A ×ˢ A) (fun ab => ab.1 * ab.2) (C * H ^ η) hfib
  apply (div_le_iff₀ hHpow).mpr
  apply (inv_mul_le_iff₀ hC).mpr
  calc
    (A.card : ℝ) ^ 2 ≤ ((A * A).card : ℝ) * (C * H ^ η) := hcount
    _ = C * (((A * A).card : ℝ) * H ^ η) := by ring

/-- For every `η > 0`, one positive constant works for all natural heights
`H ≥ 1` and all finite sets of positive naturals with every element at most
`H`. This is a height-restricted result, not the unrestricted sum-product
conjecture. -/
theorem exists_product_card_lower_bound_of_height (η : ℝ) (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧ ∀ (A : Finset ℕ) (H : ℕ), 1 ≤ H →
      (∀ a ∈ A, 0 < a) → (∀ a ∈ A, a ≤ H) →
      c * (A.card : ℝ) ^ 2 / (H : ℝ) ^ η ≤ ((A * A).card : ℝ) := by
  obtain ⟨c, hc, hbound⟩ := exists_product_card_lower_bound_of_real_height η hη
  refine ⟨c, hc, fun A H hH hpos hheight => ?_⟩
  exact hbound A (H : ℝ) (by exact_mod_cast hH) hpos
    (fun a ha => by exact_mod_cast hheight a ha)

/-- Fixed-polynomial-height corollary. For each fixed `K > 0` and `ε > 0`,
there is a positive constant depending only on these two parameters. It
works for every nonempty finite set of positive naturals whose maximum is
at most `|A|^K`.

For a nonempty set, `A.sup id` is its maximum. Nonemptiness also avoids the
empty-set obstruction `0^0 = 1` when `ε = 2`. No restriction `ε < 1` is
needed for this nonempty-set statement. -/
theorem exists_product_card_lower_bound_of_polynomial_height
    (K ε : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : Finset ℕ, A.Nonempty →
      (∀ a ∈ A, 0 < a) → ((A.sup id : ℕ) : ℝ) ≤ (A.card : ℝ) ^ K →
      c * (A.card : ℝ) ^ (2 - ε) ≤ ((A * A).card : ℝ) := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_product_card_lower_bound_of_real_height (ε / K) (div_pos hε hK)
  refine ⟨c, hc, fun A hA hpos hheight => ?_⟩
  have hN : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hN1 : (1 : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hA.card_pos)
  have hheight' : ∀ a ∈ A, (a : ℝ) ≤ (A.card : ℝ) ^ K := by
    intro a ha
    calc
      (a : ℝ) ≤ ((A.sup id : ℕ) : ℝ) := by
        exact_mod_cast (Finset.le_sup (f := id) ha)
      _ ≤ (A.card : ℝ) ^ K := hheight
  have h := hbound A ((A.card : ℝ) ^ K) (Real.one_le_rpow hN1 hK.le) hpos hheight'
  have hpower : ((A.card : ℝ) ^ K) ^ (ε / K) = (A.card : ℝ) ^ ε := by
    rw [← Real.rpow_mul hN.le, mul_div_cancel₀ ε hK.ne']
  rw [hpower] at h
  calc
    c * (A.card : ℝ) ^ (2 - ε) = c * (A.card : ℝ) ^ 2 / (A.card : ℝ) ^ ε := by
      rw [Real.rpow_sub hN, Real.rpow_two, mul_div_assoc]
    _ ≤ ((A * A).card : ℝ) := h

/-- In the range `0 < ε < 2`, the polynomial-height corollary also allows
the empty set. In particular, this covers the usual range `0 < ε < 1`.
The constant is still chosen before `A`, and may depend on both `K` and `ε`. -/
theorem exists_product_card_lower_bound_of_polynomial_height_lt_two
    (K ε : ℝ) (hK : 0 < K) (hε : 0 < ε) (hε2 : ε < 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : Finset ℕ,
      (∀ a ∈ A, 0 < a) → ((A.sup id : ℕ) : ℝ) ≤ (A.card : ℝ) ^ K →
      c * (A.card : ℝ) ^ (2 - ε) ≤ ((A * A).card : ℝ) := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_product_card_lower_bound_of_polynomial_height K ε hK hε
  refine ⟨c, hc, fun A hpos hheight => ?_⟩
  by_cases hA : A.Nonempty
  · exact hbound A hA hpos hheight
  · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    simp [Real.zero_rpow (by linarith : (2 : ℝ) - ε ≠ 0)]

end Erdos52.BoundedHeight

#print axioms Erdos52.BoundedHeight.exists_divisors_card_le_rpow
#print axioms Erdos52.BoundedHeight.exists_product_card_lower_bound_of_real_height
#print axioms Erdos52.BoundedHeight.exists_product_card_lower_bound_of_height
#print axioms Erdos52.BoundedHeight.exists_product_card_lower_bound_of_polynomial_height
#print axioms Erdos52.BoundedHeight.exists_product_card_lower_bound_of_polynomial_height_lt_two
