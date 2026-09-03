import FormalConjecturesUtil

/-!
# Erdős Problem 564

*Reference:* [erdosproblems.com/564](https://www.erdosproblems.com/564)
-/

namespace Erdos564

open Combinatorics Real Filter

/-- The untyped coefficient in the submitted expression is a natural number. -/
theorem erdos_564_iff :
    (∃ c > 0, ∀ᶠ n in atTop, (2 : ℝ)^(2 : ℝ)^(c * n) ≤ hypergraphRamsey 3 n) ↔
    ∀ᶠ n in atTop, 2 ^ (2 ^ n) ≤ hypergraphRamsey 3 n := by
  constructor
  · rintro ⟨c, hc, h⟩
    filter_upwards [h] with n hn
    have hpow : (2 : ℝ) ^ ((2 : ℝ) ^ n) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (c * n)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_left n hc))
    have hle : (2 : ℝ) ^ ((2 : ℝ) ^ n) ≤ (hypergraphRamsey 3 n : ℝ) := hpow.trans hn
    have hcast : ((2 ^ (2 ^ n) : ℕ) : ℝ) = (2 : ℝ) ^ ((2 : ℝ) ^ n) := by
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      rw [← Real.rpow_natCast]
      simp
    rw [← hcast] at hle
    exact_mod_cast hle
  · intro h
    refine ⟨1, by omega, ?_⟩
    filter_upwards [h] with n hn
    simp only [one_mul]
    have hcast : ((2 ^ (2 ^ n) : ℕ) : ℝ) = (2 : ℝ) ^ ((2 : ℝ) ^ n) := by
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      rw [← Real.rpow_natCast]
      simp
    rw [← hcast]
    exact_mod_cast hn

/-- The exact negation requires counterexamples above every natural-number threshold. -/
theorem not_erdos_564_iff :
    (¬ ∃ c > 0, ∀ᶠ n in atTop, (2 : ℝ)^(2 : ℝ)^(c * n) ≤ hypergraphRamsey 3 n) ↔
    ∀ N : ℕ, ∃ n ≥ N, hypergraphRamsey 3 n < 2 ^ (2 ^ n) := by
  rw [erdos_564_iff, Filter.eventually_atTop]
  push_neg
  rfl

/-- An upper bound with real coefficient below one refutes the formal conjecture. -/
theorem not_erdos_564_of_upper_bound
    (a : ℝ) (ha : a < 1)
    (h : ∀ᶠ n : ℕ in atTop,
      (hypergraphRamsey 3 n : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (a * (n : ℝ)))) :
    ¬ ∃ c > 0, ∀ᶠ n in atTop,
      (2 : ℝ) ^ (2 : ℝ) ^ (c * n) ≤ hypergraphRamsey 3 n := by
  rintro ⟨c, hc, hclower⟩
  obtain ⟨n, hu, hl, hn⟩ :=
    (h.and (hclower.and (eventually_gt_atTop (0 : ℕ)))).exists
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcn : (n : ℝ) ≤ ((c * n : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left n hc
  have hm : a * (n : ℝ) < ((c * n : ℕ) : ℝ) := by
    have : a * (n : ℝ) < (n : ℝ) := by nlinarith
    exact this.trans_le hcn
  have hi : (2 : ℝ) ^ (a * (n : ℝ)) < (2 : ℝ) ^ (c * n) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hm
  have ho : (2 : ℝ) ^ ((2 : ℝ) ^ (a * (n : ℝ))) <
      (2 : ℝ) ^ ((2 : ℝ) ^ (c * n)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hi
  exact (not_lt_of_ge (hl.trans hu)) ho

/--
Let $R_3(n)$ be the minimal $m$ such that if the edges of the $3$-uniform hypergraph on $m$
vertices are $2$-coloured then there is a monochromatic copy of the complete $3$-uniform
hypergraph on $n$ vertices.

Is there some constant $c>0$ such that
$$ R_3(n) \geq 2^{2^{cn}}? $$
-/
theorem erdos_564 : 
    ∃ c > 0, ∀ᶠ n in atTop, (2 : ℝ)^(2 : ℝ)^(c * n) ≤ hypergraphRamsey 3 n := by
  apply erdos_564_iff.mpr
  -- Remaining goal: ∀ᶠ n : ℕ in atTop, 2 ^ (2 ^ n) ≤ hypergraphRamsey 3 n.
  sorry

end Erdos564
