import Submission.CriticalRooting

/-!
# A conditional bridge at the critical oriented scale

The exact `r = 4` lower-bound assertion in Erdős Problem 714 implies an
asymptotic lower bound for oriented-`K_{3,4}`-free relations on `q^4` by `q^3`
vertices. The proof uses only the finite reduction in `CriticalRooting` and
arithmetic; no extremal upper bound is needed.

The vanishing hypothesis introduced below concerns **all** such relations,
not merely ones obtained by rooting a graph. It is an unproved hypothesis,
not an axiom or a theorem of this file. The final negation of the all-`r`
assertion is strictly conditional on that hypothesis. This does not settle
the conjecture. In particular, this file does not import `Submission.Spec`.
-/

namespace CriticalAsymptotic

open Filter SimpleGraph CriticalRooting

/-- The real exponent in the exact `r = 4` assertion becomes an integer
exponent on the fourth-power subsequence, including at `q = 0`. -/
theorem fourth_power_rpow (q : ℕ) :
    ((q ^ 4 : ℕ) : ℝ) ^ ((2 : ℝ) - 1 / (4 : ℝ)) = (q : ℝ) ^ 7 := by
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg q)]
  norm_num

/-- A direct estimate for the minimum and the natural division/subtraction
losses. The condition `1 ≤ b*q^3` absorbs both integer rounding losses. -/
theorem critical_quotient_bound {q E : ℕ} {b : ℝ}
    (hq : 0 < q) (hb : 0 < b) (hb1 : b ≤ 1)
    (hlarge : 1 ≤ b * (q : ℝ) ^ 3)
    (hE : 4 * b * (q : ℝ) ^ 7 ≤ (E : ℝ)) :
    let d := E / q ^ 4
    b ^ 2 * (q : ℝ) ^ 6 ≤ (min (q ^ 3) d * (d - 1) : ℕ) := by
  let d := E / q ^ 4
  change b ^ 2 * (q : ℝ) ^ 6 ≤ (min (q ^ 3) d * (d - 1) : ℕ)
  have hupper : (E : ℝ) < (q : ℝ) ^ 4 * ((d : ℝ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ E (pow_pos hq 4)
  have hd : 4 * b * (q : ℝ) ^ 3 < (d : ℝ) + 1 := by
    apply (mul_lt_mul_iff_right₀ (pow_pos (Nat.cast_pos.mpr hq : (0 : ℝ) < q) 4)).mp
    calc
      (q : ℝ) ^ 4 * (4 * b * (q : ℝ) ^ 3) = 4 * b * (q : ℝ) ^ 7 := by ring
      _ ≤ (E : ℝ) := hE
      _ < _ := hupper
  have hd1 : 1 ≤ d := by
    have : (1 : ℝ) ≤ (d : ℝ) := by nlinarith
    exact_mod_cast this
  have hsub : b * (q : ℝ) ^ 3 ≤ ((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hd1, Nat.cast_one]
    nlinarith
  have hmin : b * (q : ℝ) ^ 3 ≤ ((min (q ^ 3) d : ℕ) : ℝ) := by
    rw [Nat.cast_min, Nat.cast_pow]
    refine le_min ?_ ?_
    · simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hb1 (pow_nonneg (Nat.cast_nonneg q) 3)
    · nlinarith
  calc
    b ^ 2 * (q : ℝ) ^ 6 = (b * (q : ℝ) ^ 3) * (b * (q : ℝ) ^ 3) := by ring
    _ ≤ ((min (q ^ 3) d : ℕ) : ℝ) * ((d - 1 : ℕ) : ℝ) :=
      mul_le_mul hmin hsub (mul_nonneg hb.le (by positivity)) (Nat.cast_nonneg _)
    _ = (min (q ^ 3) d * (d - 1) : ℕ) := by rw [Nat.cast_mul]

/-- Quantitative form of the bridge: `b = min (c/4) (1/4)` yields coefficient
`b^2 > 0`. The hypothesis has exactly the exponent used by Spec at `r = 4`. -/
theorem eventually_dense_of_r4_lower_bound {c : ℝ} (hc : 0 < c)
    (hE : ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (4 : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ)) :
    ∀ᶠ q : ℕ in atTop,
      ∃ R : Fin (q ^ 4) → Fin (q ^ 3) → Prop, ∃ _ : DecidableRel R,
        OrientedFree 3 4 R ∧
          (min (c / 4) (1 / 4)) ^ 2 * (q : ℝ) ^ 6 ≤ (edgeCount R : ℝ) := by
  let b : ℝ := min (c / 4) (1 / 4)
  have hb : 0 < b := lt_min (div_pos hc (by norm_num)) (by norm_num)
  have hb1 : b ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hbc : 4 * b ≤ c := by
    have : b ≤ c / 4 := min_le_left _ _
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hE
  obtain ⟨B, hB⟩ := exists_nat_ge (1 / b)
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop B,
    eventually_ge_atTop (1 : ℕ)] with q hqN hqB hq1
  have hq : 0 < q := by omega
  have hlarge : 1 ≤ b * (q : ℝ) ^ 3 := by
    have hBq : (B : ℝ) ≤ (q : ℝ) ^ 3 := by
      exact_mod_cast hqB.trans (Nat.le_pow (by norm_num : 0 < 3))
    have := (div_le_iff₀ hb).mp (hB.trans hBq)
    simpa only [mul_comm] using this
  have hEq : c * (q : ℝ) ^ 7 ≤
      (extremalNumber (q ^ 4) (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ) := by
    simpa only [fourth_power_rpow] using
      hN (q ^ 4) (hqN.trans (Nat.le_pow (by norm_num : 0 < 4)))
  have hE4 : 4 * b * (q : ℝ) ^ 7 ≤
      (extremalNumber (q ^ 4) (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ) :=
    (mul_le_mul_of_nonneg_right hbc (by positivity)).trans hEq
  obtain ⟨R, hDec, hfree, hedge⟩ := critical_finite_reduction hq
  letI := hDec
  refine ⟨R, hDec, hfree, ?_⟩
  exact (critical_quotient_bound hq hb hb1 hlarge hE4).trans (by exact_mod_cast hedge)

/-- The exact `r = 4` instance implies a positive critical-scale density
for some oriented-free relation at every sufficiently large integer `q`. -/
theorem critical_asymptotic_bridge
    (h4 : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (4 : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ)) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ q : ℕ in atTop,
      ∃ R : Fin (q ^ 4) → Fin (q ^ 3) → Prop, ∃ _ : DecidableRel R,
        OrientedFree 3 4 R ∧ a * (q : ℝ) ^ 6 ≤ (edgeCount R : ℝ) := by
  obtain ⟨c, hc, hE⟩ := h4
  refine ⟨(min (c / 4) (1 / 4)) ^ 2, ?_, eventually_dense_of_r4_lower_bound hc hE⟩
  positivity

/-- **Unproved hypothesis**, in zero-liminf form: at arbitrarily large common
values of `q`, every oriented-`K_{3,4}`-free `q^4`-by-`q^3` relation has fewer
than `a*q^6` edges, for each positive `a`. The chosen `q` may depend on `a` and
`Q`, but not on `R`. There is no rooting, symmetry, or other restriction on
`R`; decidability only permits the finite edge count to be evaluated. -/
def OrientedCriticalZeroLiminf : Prop :=
  ∀ a : ℝ, 0 < a → ∀ Q : ℕ, ∃ q : ℕ, Q ≤ q ∧
    ∀ (R : Fin (q ^ 4) → Fin (q ^ 3) → Prop) [DecidableRel R],
      OrientedFree 3 4 R → (edgeCount R : ℝ) < a * (q : ℝ) ^ 6

/-- The zero-liminf hypothesis is incompatible with positive eventual
critical-scale density. The eventual threshold is also used in the
zero-liminf hypothesis, so both edge bounds hold at the very same `q`. -/
theorem not_eventually_dense_of_zero_liminf (hvan : OrientedCriticalZeroLiminf) :
    ¬ (∃ a : ℝ, 0 < a ∧ ∀ᶠ q : ℕ in atTop,
      ∃ R : Fin (q ^ 4) → Fin (q ^ 3) → Prop, ∃ _ : DecidableRel R,
        OrientedFree 3 4 R ∧ a * (q : ℝ) ^ 6 ≤ (edgeCount R : ℝ)) := by
  rintro ⟨a, ha, hdense⟩
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 hdense
  obtain ⟨q, hq, hupper⟩ := hvan a ha Q
  obtain ⟨R, hDec, hfree, hedge⟩ := hQ q hq
  letI := hDec
  exact (not_lt_of_ge hedge) (hupper R hfree)

/-- CONDITIONAL negation of the exact `r = 4` lower-bound assertion. -/
theorem not_r4_of_zero_liminf (hvan : OrientedCriticalZeroLiminf) :
    ¬ (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (4 : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin 4) (Fin 4)) : ℝ)) := by
  intro h4
  exact not_eventually_dense_of_zero_liminf hvan (critical_asymptotic_bridge h4)

/-- CONDITIONAL exact negation of Spec's all-`r` formula, written literally
rather than referring to Spec or its theorem. The essential vanishing
hypothesis is an explicit argument and is NOT proved here. -/
theorem not_all_r_of_zero_liminf (hvan : OrientedCriticalZeroLiminf) :
    ¬ (∀ r : ℕ, 2 ≤ r → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
        (extremalNumber n (completeBipartiteGraph (Fin r) (Fin r)) : ℝ)) := by
  intro hall
  exact not_r4_of_zero_liminf hvan (hall 4 (by norm_num))

end CriticalAsymptotic
