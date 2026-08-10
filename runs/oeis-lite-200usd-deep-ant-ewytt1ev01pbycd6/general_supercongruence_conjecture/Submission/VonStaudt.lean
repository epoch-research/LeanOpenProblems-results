import Mathlib

/-!
# Von Staudt–Clausen p-integrality bound for Bernoulli numbers

We prove the p-integrality bound coming from the von Staudt–Clausen theorem:
for every prime `p` and every `m`, the `p`-adic valuation of the `m`-th Bernoulli
number is at least `-1`, i.e. `p` occurs in the denominator of `bernoulli m` to
order at most one.

The proof uses Faulhaber's formula `sum_range_pow` applied with upper bound the
prime `p`, isolating the `i = m` term (which equals `p * bernoulli m`), and a
strong induction bounding the `p`-adic valuation of every lower term.
-/

open Nat Finset

namespace VonStaudt

/-- If two rationals both have nonnegative `p`-adic valuation, so does their sum. -/
lemma padicValRat_add_nonneg {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : 0 ≤ padicValRat p x) (hy : 0 ≤ padicValRat p y) :
    0 ≤ padicValRat p (x + y) := by
  by_cases h : x + y = 0
  · simp [h]
  · exact le_trans (le_min hx hy) (padicValRat.min_le_padicValRat_add h)

/-- A finite sum of rationals of nonnegative `p`-adic valuation has nonnegative valuation. -/
lemma padicValRat_sum_nonneg {p : ℕ} [Fact p.Prime] {s : Finset ℕ} {F : ℕ → ℚ}
    (hF : ∀ i ∈ s, 0 ≤ padicValRat p (F i)) :
    0 ≤ padicValRat p (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      refine padicValRat_add_nonneg (hF a (by simp)) (ih (fun i hi => hF i (by simp [hi])))

/-- The `p`-adic valuation of a natural-number power `(k : ℚ) ^ m` is nonnegative. -/
lemma padicValRat_natCast_pow_nonneg {p : ℕ} [Fact p.Prime] (k m : ℕ) :
    0 ≤ padicValRat p ((k : ℚ) ^ m) := by
  have : ((k : ℚ) ^ m) = ((k ^ m : ℕ) : ℚ) := by push_cast; ring
  rw [this]
  exact zero_le_padicValRat_of_nat _

/-- **Von Staudt–Clausen p-integrality bound.** For every prime `p` and every `m`, the
`p`-adic valuation of the `m`-th Bernoulli number is at least `-1`. Equivalently, `p`
occurs in the denominator of `bernoulli m` to order at most one. -/
theorem padicValRat_bernoulli_ge_neg_one (p : ℕ) [Fact p.Prime] (m : ℕ) :
    (-1 : ℤ) ≤ padicValRat p (bernoulli m) := by
  have hp : p.Prime := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    -- The term appearing in Faulhaber's formula.
    set G : ℕ → ℚ := fun i =>
      bernoulli i * ((m + 1).choose i : ℚ) * (p : ℚ) ^ (m + 1 - i) / ((m : ℚ) + 1) with hG
    -- Each lower term `G i` (for `i < m`) is a `p`-adic integer.
    have hGnonneg : ∀ i, i < m → 0 ≤ padicValRat p (G i) := by
      intro i hi
      simp only [hG]
      by_cases hb : bernoulli i = 0
      · simp [hb]
      · have hC1nat : (m + 1).choose i ≠ 0 := (Nat.choose_pos (by omega)).ne'
        have hC1 : ((m + 1).choose i : ℚ) ≠ 0 := by exact_mod_cast hC1nat
        have hP : (p : ℚ) ^ (m + 1 - i) ≠ 0 := pow_ne_zero _ hpQ
        have hD : ((m : ℚ) + 1) ≠ 0 := by positivity
        rw [padicValRat.div (mul_ne_zero (mul_ne_zero hb hC1) hP) hD,
            padicValRat.mul (mul_ne_zero hb hC1) hP,
            padicValRat.mul hb hC1,
            padicValRat.pow hpQ, padicValRat.self hp1, mul_one]
        -- rewrite valuations of naturals
        rw [padicValRat.of_nat (n := (m + 1).choose i)]
        have hDeq : ((m : ℚ) + 1) = ((m + 1 : ℕ) : ℚ) := by push_cast; ring
        rw [hDeq, padicValRat.of_nat (n := m + 1)]
        -- the multiplicative choose identity, taken p-adic valuations
        have hnat : (m + 1).choose i * (m + 1 - i) = m.choose i * (m + 1) :=
          (Nat.choose_mul_succ_eq m i).symm
        have hval := congrArg (padicValNat p) hnat
        rw [padicValNat.mul hC1nat (by omega : m + 1 - i ≠ 0),
            padicValNat.mul (Nat.choose_pos (by omega)).ne' (Nat.succ_ne_zero m)] at hval
        simp only [Nat.succ_eq_add_one] at hval
        -- the bound `v_p(j) < j` for `j = m + 1 - i ≥ 1`
        have hj : padicValNat p (m + 1 - i) < m + 1 - i := by
          have h1 : padicValNat p (m + 1 - i) < p ^ padicValNat p (m + 1 - i) :=
            Nat.lt_pow_self hp1
          have h2 : p ^ padicValNat p (m + 1 - i) ≤ m + 1 - i :=
            Nat.le_of_dvd (by omega) pow_padicValNat_dvd
          omega
        have hbv : (-1 : ℤ) ≤ padicValRat p (bernoulli i) := ih i hi
        -- conclude by linear arithmetic over ℤ
        omega
    -- Faulhaber's formula with upper bound the prime `p`.
    have hFaul := sum_range_pow p m
    -- isolate the top term `G m`, which equals `bernoulli m * p`.
    rw [Finset.sum_range_succ] at hFaul
    have hGm : G m = bernoulli m * (p : ℚ) := by
      have hD : ((m : ℚ) + 1) ≠ 0 := by positivity
      simp only [hG, Nat.choose_succ_self_right, Nat.add_sub_cancel_left, pow_one]
      push_cast
      field_simp
    -- rewrite Faulhaber to match our `G`.
    have hfold : (∑ k ∈ range p, (k : ℚ) ^ m)
        = (∑ i ∈ range m, G i) + bernoulli m * (p : ℚ) := by
      rw [← hGm]
      convert hFaul using 2
    -- therefore `bernoulli m * p = (integer sum) - ∑ lower terms`.
    have hkey : bernoulli m * (p : ℚ)
        = (∑ k ∈ range p, (k : ℚ) ^ m) + (∑ i ∈ range m, -(G i)) := by
      rw [Finset.sum_neg_distrib]
      rw [hfold]; ring
    -- both summands are `p`-adic integers.
    have hInt : 0 ≤ padicValRat p (bernoulli m * (p : ℚ)) := by
      rw [hkey]
      refine padicValRat_add_nonneg ?_ ?_
      · exact padicValRat_sum_nonneg (fun k _ => padicValRat_natCast_pow_nonneg k m)
      · refine padicValRat_sum_nonneg (fun i hi => ?_)
        rw [padicValRat.neg]
        exact hGnonneg i (Finset.mem_range.mp hi)
    -- conclude the bound on `bernoulli m`.
    by_cases hbm : bernoulli m = 0
    · simp [hbm]
    · rw [padicValRat.mul hbm hpQ, padicValRat.self hp1] at hInt
      omega

end VonStaudt
