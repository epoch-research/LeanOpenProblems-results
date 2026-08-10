import FormalConjectures.Util.ProblemImports

open Finset

section Helpers

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Step B: the sum of the quadratic character over squares. -/
private lemma char_sum_sq :
    ∑ x : F, quadraticChar F (x ^ 2) = (Fintype.card F : ℤ) - 1 := by
  have h1 : ∀ x : F, quadraticChar F (x ^ 2) = (if x = 0 then (0 : ℤ) else 1) := by
    intro x
    rcases eq_or_ne x 0 with h | h
    · subst h
      rw [show (0 : F) ^ 2 = 0 from by ring, quadraticChar_zero]
      simp
    · rw [if_neg h]; exact quadraticChar_sq_one' h
  have e1 : ∑ x : F, (if x = 0 then (1 : ℤ) else 0) = 1 := by simp
  have e2 : ∑ _x : F, (1 : ℤ) = (Fintype.card F : ℤ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  calc ∑ x : F, quadraticChar F (x ^ 2)
      = ∑ x : F, (if x = 0 then (0 : ℤ) else 1) := Finset.sum_congr rfl (fun x _ => h1 x)
    _ = ∑ x : F, ((1 : ℤ) - (if x = 0 then 1 else 0)) := by
        apply Finset.sum_congr rfl; intro x _; by_cases hx : x = 0 <;> simp [hx]
    _ = (∑ _x : F, (1 : ℤ)) - ∑ x : F, (if x = 0 then (1 : ℤ) else 0) := by
        rw [Finset.sum_sub_distrib]
    _ = (Fintype.card F : ℤ) - 1 := by rw [e1, e2]

/-- Step B + C combined: with the linear term removed. -/
private lemma char_sum_sq_add (hF : ringChar F ≠ 2) (δ : F) :
    ∑ x : F, quadraticChar F (x ^ 2 + δ) =
      if δ = 0 then (Fintype.card F : ℤ) - 1 else -1 := by
  by_cases hδ : δ = 0
  · subst hδ; simpa using char_sum_sq
  · rw [if_neg hδ]
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
    -- The number of square roots of `a`, as a filter cardinality.
    have hcard : ∀ x : F, (quadraticChar F (x ^ 2 + δ) + 1 : ℤ)
        = ((univ.filter (fun y => y ^ 2 = x ^ 2 + δ)).card : ℤ) := by
      intro x
      rw [← quadraticChar_card_sqrts hF (x ^ 2 + δ), Set.toFinset_setOf]
    -- Fubini: rewrite the double count as a count over the product type.
    have hfub : (univ.filter (fun p : F × F => p.2 ^ 2 = p.1 ^ 2 + δ)).card
        = ∑ x : F, (univ.filter (fun y => y ^ 2 = x ^ 2 + δ)).card := by
      rw [Finset.card_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.card_filter]
    -- Bijection `(x, y) ↦ (y - x, y + x)` turning `y² - x² = δ` into `u * v = δ`.
    have hbij : (univ.filter (fun p : F × F => p.2 ^ 2 = p.1 ^ 2 + δ)).card
        = (univ.filter (fun q : F × F => q.1 * q.2 = δ)).card := by
      apply Finset.card_nbij' (fun p : F × F => (p.2 - p.1, p.2 + p.1))
                              (fun q : F × F => ((q.2 - q.1) / 2, (q.2 + q.1) / 2))
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        rw [show (p.2 - p.1) * (p.2 + p.1) = p.2 ^ 2 - p.1 ^ 2 from by ring, hp]; ring
      · intro q hq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        have key : ((q.2 + q.1) / 2) ^ 2 - ((q.2 - q.1) / 2) ^ 2 = q.1 * q.2 := by
          rw [div_pow, div_pow, div_sub_div_same, div_eq_iff (pow_ne_zero 2 h2)]; ring
        rw [← hq, ← key]; ring
      · intro p _
        have e1 : ((p.2 + p.1) - (p.2 - p.1)) / 2 = p.1 := by rw [div_eq_iff h2]; ring
        have e2 : ((p.2 + p.1) + (p.2 - p.1)) / 2 = p.2 := by rw [div_eq_iff h2]; ring
        show (((p.2 + p.1) - (p.2 - p.1)) / 2, ((p.2 + p.1) + (p.2 - p.1)) / 2) = p
        rw [e1, e2]
      · intro q _
        have e1 : (q.2 + q.1) / 2 - (q.2 - q.1) / 2 = q.1 := by
          rw [div_sub_div_same, div_eq_iff h2]; ring
        have e2 : (q.2 + q.1) / 2 + (q.2 - q.1) / 2 = q.2 := by
          rw [← add_div, div_eq_iff h2]; ring
        show ((q.2 + q.1) / 2 - (q.2 - q.1) / 2, (q.2 + q.1) / 2 + (q.2 - q.1) / 2) = q
        rw [e1, e2]
    -- Count of solutions of `u * v = δ` for `δ ≠ 0`.
    have hcount : (univ.filter (fun q : F × F => q.1 * q.2 = δ)).card = Fintype.card F - 1 := by
      have hcard_ne : (univ.filter (fun u : F => u ≠ 0)).card = Fintype.card F - 1 := by
        rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
      rw [← hcard_ne]
      apply Finset.card_nbij' (fun q : F × F => q.1) (fun u : F => (u, δ / u))
      · intro q hq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        intro h0
        rw [h0, zero_mul] at hq
        exact hδ hq.symm
      · intro u hu
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        exact mul_div_cancel₀ δ hu
      · intro q hq
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        have hq1 : q.1 ≠ 0 := by
          intro h0; rw [h0, zero_mul] at hq; exact hδ hq.symm
        show (q.1, δ / q.1) = q
        have : δ / q.1 = q.2 := by rw [div_eq_iff hq1, ← hq]; ring
        rw [this]
      · intro u hu
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu
        show ((u, δ / u) : F × F).1 = u
        rfl
    -- Assemble.
    have hsum1 : (∑ x : F, (quadraticChar F (x ^ 2 + δ) + 1)) = (Fintype.card F : ℤ) - 1 := by
      have heq : (∑ x : F, (quadraticChar F (x ^ 2 + δ) + 1))
          = (((∑ x : F, (univ.filter (fun y => y ^ 2 = x ^ 2 + δ)).card) : ℕ) : ℤ) := by
        rw [Nat.cast_sum]
        exact Finset.sum_congr rfl (fun x _ => hcard x)
      rw [heq, ← hfub, hbij, hcount, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
    have hone : ∑ _x : F, (1 : ℤ) = (Fintype.card F : ℤ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hsplit : (∑ x : F, (quadraticChar F (x ^ 2 + δ) + 1))
        = (∑ x : F, quadraticChar F (x ^ 2 + δ)) + (Fintype.card F : ℤ) := by
      rw [Finset.sum_add_distrib, hone]
    rw [hsplit] at hsum1
    linarith

end Helpers

/-- Sum of the quadratic character over a monic quadratic polynomial.
If the discriminant β²-4γ is zero the sum is (card F) - 1, otherwise it is -1. -/
theorem char_sum_quadratic {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (β γ : F) :
    ∑ x : F, quadraticChar F (x^2 + β*x + γ) =
      if β^2 - 4*γ = 0 then (Fintype.card F : ℤ) - 1 else -1 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 from by norm_num]; exact mul_ne_zero h2 h2
  -- Complete the square: reindex `x ↦ x + β/2`.
  have key : ∑ x : F, quadraticChar F (x ^ 2 + β * x + γ)
      = ∑ x : F, quadraticChar F (x ^ 2 + (γ - β ^ 2 / 4)) := by
    apply Fintype.sum_equiv (Equiv.addRight (β / 2))
    intro x
    simp only [Equiv.coe_addRight]
    congr 1
    field_simp
    ring
  -- Discriminant condition is equivalent.
  have hiff : (β ^ 2 - 4 * γ = 0) ↔ (γ - β ^ 2 / 4 = 0) := by
    rw [sub_eq_zero, sub_eq_zero, eq_div_iff h4]
    constructor <;> intro h <;> linear_combination -h
  rw [key, char_sum_sq_add hF (γ - β ^ 2 / 4)]
  by_cases h : β ^ 2 - 4 * γ = 0
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
