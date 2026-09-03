import FormalConjecturesUtil

/-!
# A partial reduction for the actual Erdős 1057 counting function

This file uses the root `IsCarmichael` definition and counts precisely the natural
numbers satisfying it.  It establishes elementary counting bounds, proves that
561 is a Carmichael number using Fermat's little theorem and coprime-modulus CRT,
and reduces the proposed logarithmic asymptotic to eventual power lower bounds.

**This is a partial reduction, NOT a solution of Erdős Problem 1057.**  In
particular, neither the asserted limit nor the family of power lower bounds is
proved unconditionally here.  This file does not import or modify `Spec.lean`.
-/

open Filter
open scoped Topology

namespace Erdos1057Research

/-- A copy of the actual Carmichael counting function in Erdős Problem 1057. -/
noncomputable def C (x : ℝ) : ℝ :=
  ({n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}.ncard : ℝ)

/-- Applying the defining property at base 1 rules out 0, 1, and primes. -/
theorem isCarmichael_gt_one_not_prime {n : ℕ} (hn : IsCarmichael n) :
    1 < n ∧ ¬ n.Prime := by
  have h : n.FermatPsp 1 := hn 1 le_rfl (by simp)
  exact ⟨h.2.2, h.2.1⟩

/-- The set counted by `C x` is finite for every real `x`, including negative `x`. -/
theorem finite_counting_set (x : ℝ) :
    Set.Finite {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x} := by
  refine (Set.finite_le_nat (Nat.floor x)).subset ?_
  intro n hn
  exact Nat.le_floor hn.2

/-- The count is nonnegative. -/
theorem C_nonneg (x : ℝ) : 0 ≤ C x := by
  unfold C
  positivity

/-- Increasing the cutoff can only increase the finite count. -/
theorem C_monotone : Monotone C := by
  intro x y hxy
  unfold C
  exact_mod_cast Set.ncard_le_ncard
    (show {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x} ⊆
        {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ y} from
      fun _ hn => ⟨hn.1, hn.2.trans hxy⟩)
    (finite_counting_set y)

/-- Excluding 0 gives an upper bound by the number of positive naturals up to `x`. -/
theorem C_le_floor (x : ℝ) : C x ≤ (Nat.floor x : ℝ) := by
  have hcard : {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}.ncard ≤ Nat.floor x := by
    calc
      {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}.ncard ≤
          (↑(Finset.Icc 1 (Nat.floor x)) : Set ℕ).ncard := by
        apply Set.ncard_le_ncard _ (Finset.finite_toSet _)
        intro n hn
        simp only [Finset.mem_coe, Finset.mem_Icc]
        exact ⟨(isCarmichael_gt_one_not_prime hn.1).1.le, Nat.le_floor hn.2⟩
      _ = Nat.floor x := by
        rw [Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel]
  unfold C
  exact_mod_cast hcard

/-- The elementary upper bound needed in the analytic reduction. -/
theorem C_le_self {x : ℝ} (hx : 0 ≤ x) : C x ≤ x :=
  (C_le_floor x).trans (Nat.floor_le hx)

/-- Raise Fermat's little theorem to an exponent divisible by `p - 1`. -/
theorem pow_modEq_one_of_prime {p b k : ℕ} (hp : p.Prime)
    (hbp : b.Coprime p) (hk : p - 1 ∣ k) : Nat.ModEq p (b ^ k) 1 := by
  obtain ⟨m, rfl⟩ := hk
  simpa only [pow_mul, one_pow] using
    (Nat.ModEq.pow_card_sub_one_eq_one hp hbp).pow m

/-- `561 = 3 * 11 * 17` is Carmichael: FLT at the three primes and CRT suffice. -/
theorem isCarmichael_561 : IsCarmichael 561 := by
  intro b hb hcop
  refine ⟨(Nat.probablePrime_iff_modEq 561 hb).2 ?_, by norm_num, by norm_num⟩
  have h3 : Nat.ModEq 3 (b ^ 560) 1 :=
    pow_modEq_one_of_prime (by norm_num)
      (hcop.coprime_dvd_left (by norm_num : 3 ∣ 561)).symm (by norm_num)
  have h11 : Nat.ModEq 11 (b ^ 560) 1 :=
    pow_modEq_one_of_prime (by norm_num)
      (hcop.coprime_dvd_left (by norm_num : 11 ∣ 561)).symm (by norm_num)
  have h17 : Nat.ModEq 17 (b ^ 560) 1 :=
    pow_modEq_one_of_prime (by norm_num)
      (hcop.coprime_dvd_left (by norm_num : 17 ∣ 561)).symm (by norm_num)
  have h33 : Nat.ModEq (3 * 11) (b ^ 560) 1 :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 11)).1 ⟨h3, h11⟩
  have h561 : Nat.ModEq ((3 * 11) * 17) (b ^ 560) 1 :=
    (Nat.modEq_and_modEq_iff_modEq_mul
      (by norm_num : Nat.Coprime (3 * 11) 17)).1 ⟨h33, h17⟩
  simpa using h561

/-- The explicit Carmichael number 561 ensures eventual positivity of the count. -/
theorem one_le_C {x : ℝ} (hx : 561 ≤ x) : 1 ≤ C x := by
  have hpos : 0 < {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x}.ncard :=
    (Set.ncard_pos (finite_counting_set x)).2 ⟨561, isCarmichael_561, by simpa using hx⟩
  unfold C
  exact_mod_cast (Nat.succ_le_of_lt hpos)

/-- Above 561, power lower bounds are exactly lower bounds on the log ratio. -/
theorem rpow_le_C_iff_log_ratio {x ε : ℝ} (hx : 561 ≤ x) :
    x ^ (1 - ε) ≤ C x ↔ 1 - ε ≤ Real.log (C x) / Real.log x := by
  have hx1 : 1 < x := by linarith
  have hC : 0 < C x := lt_of_lt_of_le zero_lt_one (one_le_C hx)
  rw [Real.rpow_le_iff_le_log (lt_trans zero_lt_one hx1) hC,
    le_div_iff₀ (Real.log_pos hx1)]

/-- The counting upper bound gives an eventual upper bound of 1 on the log ratio. -/
theorem log_ratio_le_one {x : ℝ} (hx : 561 ≤ x) :
    Real.log (C x) / Real.log x ≤ 1 := by
  have hx1 : 1 < x := by linarith
  have hC : 0 < C x := lt_of_lt_of_le zero_lt_one (one_le_C hx)
  apply (div_le_iff₀ (Real.log_pos hx1)).2
  rw [one_mul]
  exact Real.log_le_log hC (C_le_self (by linarith))

/--
The rigorous analytic reduction for the actual count: the proposed logarithmic
limit is equivalent to every fixed power lower bound of exponent less than 1.
This equivalence proves neither side unconditionally.
-/
theorem log_ratio_tendsto_one_iff :
    Tendsto (fun x : ℝ => Real.log (C x) / Real.log x) atTop (𝓝 1) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, x ^ (1 - ε) ≤ C x := by
  constructor
  · intro h ε hε
    have hlower : ∀ᶠ x : ℝ in atTop,
        1 - ε < Real.log (C x) / Real.log x :=
      (tendsto_order.1 h).1 (1 - ε) (by linarith)
    filter_upwards [hlower, eventually_ge_atTop (561 : ℝ)] with x hlower hx
    exact (rpow_le_C_iff_log_ratio hx).2 hlower.le
  · intro hlower
    apply tendsto_order.2
    constructor
    · intro a ha
      have hε : 0 < (1 - a) / 2 := by linarith
      filter_upwards [hlower ((1 - a) / 2) hε,
        eventually_ge_atTop (561 : ℝ)] with x hpow hx
      have hratio := (rpow_le_C_iff_log_ratio hx).1 hpow
      linarith
    · intro a ha
      filter_upwards [eventually_ge_atTop (561 : ℝ)] with x hx
      exact (log_ratio_le_one hx).trans_lt ha

/-- The same reduction with explicit sufficiently-large real thresholds. -/
theorem log_ratio_tendsto_one_iff_threshold :
    Tendsto (fun x : ℝ => Real.log (C x) / Real.log x) atTop (𝓝 1) ↔
      ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → x ^ (1 - ε) ≤ C x := by
  rw [log_ratio_tendsto_one_iff]
  simp only [Filter.eventually_atTop]

end Erdos1057Research

-- Kernel-axiom audit of every theorem in this file.
#print axioms Erdos1057Research.isCarmichael_gt_one_not_prime
#print axioms Erdos1057Research.finite_counting_set
#print axioms Erdos1057Research.C_nonneg
#print axioms Erdos1057Research.C_monotone
#print axioms Erdos1057Research.C_le_floor
#print axioms Erdos1057Research.C_le_self
#print axioms Erdos1057Research.pow_modEq_one_of_prime
#print axioms Erdos1057Research.isCarmichael_561
#print axioms Erdos1057Research.one_le_C
#print axioms Erdos1057Research.rpow_le_C_iff_log_ratio
#print axioms Erdos1057Research.log_ratio_le_one
#print axioms Erdos1057Research.log_ratio_tendsto_one_iff
#print axioms Erdos1057Research.log_ratio_tendsto_one_iff_threshold
