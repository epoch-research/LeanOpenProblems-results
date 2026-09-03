import FormalConjecturesUtil

/-!
# Rational exponents from an eventual polynomial relation

A sequence asymptotic to `c * n ^ a`, with `c > 0`, has rational exponent if it
satisfies a fixed nonzero bivariate polynomial relation eventually. We express
the polynomial as a nonempty finite set of distinct monomials with nonzero
real coefficients.

This is only an algebraic endgame: no polynomial relation for graph extremal
numbers is constructed or assumed to exist without an explicit hypothesis.
-/

open Filter Asymptotics
open scoped Topology

namespace Erdos713Polynomial

/-- At an irrational exponent, distinct monomials have distinct growth weights. -/
lemma monomial_weight_injective {a : ℝ}
    (ha : a ∉ Set.range ((↑) : ℚ → ℝ)) :
    Function.Injective (fun p : ℕ × ℕ => (p.1 : ℝ) + a * (p.2 : ℝ)) := by
  intro p q hpq
  dsimp only at hpq
  by_cases h₂ : p.2 = q.2
  · apply Prod.ext _ h₂
    have h₁ : (p.1 : ℝ) = q.1 := by
      rw [h₂] at hpq
      linarith
    exact_mod_cast h₁
  · exfalso
    apply ha
    refine ⟨((q.1 : ℚ) - p.1) / ((p.2 : ℚ) - q.2), ?_⟩
    push_cast
    have hden : (p.2 : ℝ) - q.2 ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast h₂)
    apply (div_eq_iff hden).mpr
    linarith

/-- Asymptotic equivalence gives the normalized ratio limit, even for negative `a`. -/
lemma tendsto_div_rpow_of_equivalent {f : ℕ → ℝ} {a c : ℝ}
    (hf : f ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ a)) :
    Tendsto (fun n : ℕ => f n / (n : ℝ) ^ a) atTop (𝓝 c) := by
  obtain ⟨u, hu, hfu⟩ := hf.exists_eq_mul
  have hu' : Tendsto (fun n => u n * c) atTop (𝓝 c) := by
    simpa only [one_mul] using hu.mul_const c
  apply hu'.congr'
  filter_upwards [hfu, eventually_gt_atTop 0] with n hn hnpos
  have hnpos' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnz : (n : ℝ) ^ a ≠ 0 := (Real.rpow_pos_of_pos hnpos' a).ne'
  change u n * c = f n / (n : ℝ) ^ a
  change f n = u n * (c * (n : ℝ) ^ a) at hn
  rw [hn, ← mul_assoc, mul_div_cancel_right₀ _ hnz]

/-- The normalization identity used on each monomial, away from `n = 0`. -/
lemma normalized_monomial {x : ℝ} (hx : 0 < x) (y b a L : ℝ) (p : ℕ × ℕ) :
    b * x ^ p.1 * y ^ p.2 / x ^ L =
      b * (y / x ^ a) ^ p.2 * x ^ ((p.1 : ℝ) + a * (p.2 : ℝ) - L) := by
  rw [Real.rpow_sub hx, Real.rpow_add hx, Real.rpow_natCast,
    Real.rpow_mul_natCast hx.le, div_pow]
  have ha : x ^ a ≠ 0 := (Real.rpow_pos_of_pos hx a).ne'
  have hL : x ^ L ≠ 0 := (Real.rpow_pos_of_pos hx L).ne'
  field_simp

/--
An eventual nonzero finite polynomial relation forces a power-law exponent to
be rational. The pairs in `s` are the distinct monomials, and all coefficients
on `s` are nonzero; thus `hs` and `hd` express that the polynomial is nonzero.

This theorem does not supply such a relation for graph extremal numbers.
-/
theorem rational_exponent_of_eventually_polynomial_eq_zero
    {f : ℕ → ℝ} {a c : ℝ}
    (hc : 0 < c)
    (hf : f ~[atTop] (fun n : ℕ => c * (n : ℝ) ^ a))
    (s : Finset (ℕ × ℕ)) (hs : s.Nonempty)
    (d : ℕ × ℕ → ℝ) (hd : ∀ p ∈ s, d p ≠ 0)
    (hP : ∀ᶠ n : ℕ in atTop,
      ∑ p ∈ s, d p * (n : ℝ) ^ p.1 * (f n) ^ p.2 = 0) :
    a ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  by_contra ha
  let w : ℕ × ℕ → ℝ := fun p => (p.1 : ℝ) + a * (p.2 : ℝ)
  have hw : Function.Injective w := monomial_weight_injective ha
  obtain ⟨p₀, hp₀, hmax⟩ := s.exists_max_image w hs
  have hratio := tendsto_div_rpow_of_equivalent hf
  -- After division by the largest power, just the unique largest monomial survives.
  have hterm : ∀ p ∈ s,
      Tendsto (fun n : ℕ =>
        d p * (n : ℝ) ^ p.1 * (f n) ^ p.2 / (n : ℝ) ^ w p₀)
        atTop (𝓝 (if p = p₀ then d p * c ^ p.2 else 0)) := by
    intro p hp
    have hbase := (hratio.pow p.2).const_mul (d p)
    have hnormalized : Tendsto (fun n : ℕ =>
        d p * (f n / (n : ℝ) ^ a) ^ p.2 * (n : ℝ) ^ (w p - w p₀))
        atTop (𝓝 (if p = p₀ then d p * c ^ p.2 else 0)) := by
      by_cases hpp : p = p₀
      · subst p
        simpa using hbase
      · have hlt : w p < w p₀ := lt_of_le_of_ne (hmax p hp) (hw.ne hpp)
        have hdecay : Tendsto (fun n : ℕ => (n : ℝ) ^ (w p - w p₀))
            atTop (𝓝 (0 : ℝ)) := by
          simpa only [neg_sub] using
            (tendsto_rpow_neg_atTop (sub_pos.mpr hlt)).comp
              (tendsto_natCast_atTop_atTop (R := ℝ))
        simpa only [if_neg hpp, mul_zero] using hbase.mul hdecay
    apply hnormalized.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    exact (normalized_monomial hn' (f n) (d p) a (w p₀) p).symm
  have hsum : Tendsto (fun n : ℕ =>
      ∑ p ∈ s, d p * (n : ℝ) ^ p.1 * (f n) ^ p.2 / (n : ℝ) ^ w p₀)
      atTop (𝓝 (d p₀ * c ^ p₀.2)) := by
    simpa [hp₀] using tendsto_finset_sum s hterm
  -- But the same normalized sum is eventually zero by the polynomial relation.
  have hzero : (fun n : ℕ =>
      ∑ p ∈ s, d p * (n : ℝ) ^ p.1 * (f n) ^ p.2 / (n : ℝ) ^ w p₀)
      =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [hP] with n hn
    rw [← Finset.sum_div, hn, zero_div]
  have hsum_zero : Tendsto (fun n : ℕ =>
      ∑ p ∈ s, d p * (n : ℝ) ^ p.1 * (f n) ^ p.2 / (n : ℝ) ^ w p₀)
      atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds.congr' hzero.symm
  exact (mul_ne_zero (hd p₀ hp₀) (pow_ne_zero _ hc.ne'))
    (tendsto_nhds_unique hsum hsum_zero)

end Erdos713Polynomial

#print axioms Erdos713Polynomial.rational_exponent_of_eventually_polynomial_eq_zero
