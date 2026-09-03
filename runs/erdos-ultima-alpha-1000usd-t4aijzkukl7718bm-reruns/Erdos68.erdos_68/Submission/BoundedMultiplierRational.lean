import FormalConjecturesUtil

/-!
# Bounded shifted multipliers can still give a rational reciprocal series

This is an auxiliary counterexample to a possible generalization, not a
proof or disproof of Erdos 68. The denominators below are not n! - 1.
-/

namespace BoundedMultiplierRational

set_option maxHeartbeats 1000000

private def lower (A q : ℚ) : ℚ := 1 / (q * A - 1) + 1 / (4 * (q * A))
private def upper (A q : ℚ) : ℚ := 1 / (q * A - 1) + 1 / (q * A)

private lemma lower_bound (A q : ℚ) (hA : 8 ≤ A) (hq : 2 ≤ q) :
    lower A q ≤ 4 / (3 * (q * A)) := by
  have hx : (16 : ℚ) ≤ q * A := by nlinarith
  have hx0 : 0 < q * A := by linarith
  have hx1 : 0 < q * A - 1 := by linarith
  have h : 1 / (q * A - 1) ≤ 13 / (12 * (q * A)) := by
    apply (div_le_div_iff₀ hx1 (by positivity)).mpr
    nlinarith
  calc
    lower A q ≤ 13 / (12 * (q * A)) + 1 / (4 * (q * A)) :=
      by unfold lower; exact add_le_add h le_rfl
    _ = 4 / (3 * (q * A)) := by ring

private lemma upper_bound (A q : ℚ) (hA : 8 ≤ A) (hq : 2 ≤ q) :
    2 / (q * A) ≤ upper A q := by
  have hx : (16 : ℚ) ≤ q * A := by nlinarith
  have h : 1 / (q * A) ≤ 1 / (q * A - 1) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  calc
    2 / (q * A) = 1 / (q * A) + 1 / (q * A) := by ring
    _ ≤ upper A q := by unfold upper; exact add_le_add h le_rfl

private lemma overlap (A q : ℚ) (hA : 8 ≤ A) (hq : 2 ≤ q) :
    lower A q ≤ upper A (q + 1) := by
  calc
    lower A q ≤ 4 / (3 * (q * A)) := lower_bound A q hA hq
    _ ≤ 2 / ((q + 1) * A) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    _ ≤ upper A (q + 1) := upper_bound A (q + 1) hA (by linarith)

private lemma lower_six (A : ℚ) (hA : 8 ≤ A) :
    lower A 6 ≤ 1 / (4 * A) := by
  have h : 1 / (6 * A - 1) ≤ 5 / (24 * A) := by
    apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
    linarith
  calc
    lower A 6 ≤ 5 / (24 * A) + 1 / (4 * (6 * A)) := by
      unfold lower
      exact add_le_add h le_rfl
    _ = 1 / (4 * A) := by ring

private lemma upper_two (A : ℚ) (hA : 8 ≤ A) :
    1 / A ≤ upper A 2 := by
  simpa only [show (2 : ℚ) / (2 * A) = 1 / A by ring] using
    upper_bound A 2 hA (by norm_num)

private lemma exists_digit (A r : ℚ) (hA : 8 ≤ A)
    (hr : 1 / (4 * A) ≤ r) (hr' : r ≤ 1 / A) :
    ∃ q : ℕ, 2 ≤ q ∧ q ≤ 6 ∧ lower A q ≤ r ∧ r ≤ upper A q := by
  have o5 : lower A 5 ≤ upper A 6 := by
    simpa only [show (5 : ℚ) + 1 = 6 by norm_num] using overlap A 5 hA (by norm_num)
  have o4 : lower A 4 ≤ upper A 5 := by
    simpa only [show (4 : ℚ) + 1 = 5 by norm_num] using overlap A 4 hA (by norm_num)
  have o3 : lower A 3 ≤ upper A 4 := by
    simpa only [show (3 : ℚ) + 1 = 4 by norm_num] using overlap A 3 hA (by norm_num)
  have o2 : lower A 2 ≤ upper A 3 := by
    simpa only [show (2 : ℚ) + 1 = 3 by norm_num] using overlap A 2 hA (by norm_num)
  by_cases h6 : r ≤ upper A 6
  · exact ⟨6, by omega, by omega, (lower_six A hA).trans hr, h6⟩
  have l5 : lower A 5 ≤ r := o5.trans (le_of_not_ge h6)
  by_cases h5 : r ≤ upper A 5
  · exact ⟨5, by omega, by omega, l5, h5⟩
  have l4 : lower A 4 ≤ r := o4.trans (le_of_not_ge h5)
  by_cases h4 : r ≤ upper A 4
  · exact ⟨4, by omega, by omega, l4, h4⟩
  have l3 : lower A 3 ≤ r := o3.trans (le_of_not_ge h4)
  by_cases h3 : r ≤ upper A 3
  · exact ⟨3, by omega, by omega, l3, h3⟩
  exact ⟨2, by omega, by omega,
    o2.trans (le_of_not_ge h3),
    hr'.trans (upper_two A hA)⟩

def Valid (A : ℕ) (r : ℚ) : Prop :=
  8 ≤ A ∧ 1 / (4 * (A : ℚ)) ≤ r ∧ r ≤ 1 / (A : ℚ)

noncomputable def digit (A : ℕ) (r : ℚ) : ℕ := by
  classical
  exact if h : Valid A r then
    Classical.choose (exists_digit A r (by exact_mod_cast h.1) h.2.1 h.2.2)
  else 2

lemma digit_spec {A : ℕ} {r : ℚ} (h : Valid A r) :
    2 ≤ digit A r ∧ digit A r ≤ 6 ∧
      lower A (digit A r) ≤ r ∧ r ≤ upper A (digit A r) := by
  classical
  simpa only [digit, dif_pos h] using
    Classical.choose_spec (exists_digit (A : ℚ) r (by exact_mod_cast h.1) h.2.1 h.2.2)

noncomputable def step (s : ℕ × ℚ) : ℕ × ℚ :=
  let B := digit s.1 s.2 * s.1
  (B, s.2 - 1 / ((B : ℚ) - 1))

lemma step_valid {A : ℕ} {r : ℚ} (h : Valid A r) :
    Valid (step (A, r)).1 (step (A, r)).2 := by
  obtain ⟨hq, hq', hl, hu⟩ := digit_spec h
  have hB : 8 ≤ digit A r * A := by nlinarith [h.1]
  unfold lower at hl
  unfold upper at hu
  refine ⟨hB, ?_, ?_⟩
  · simp only [step, Nat.cast_mul]
    linarith
  · simp only [step, Nat.cast_mul]
    linarith

noncomputable def state (n : ℕ) : ℕ × ℚ := (step^[n]) (8, (1 / 16 : ℚ))

lemma state_succ (n : ℕ) : state (n + 1) = step (state n) :=
  Function.iterate_succ_apply' _ _ _

lemma state_valid (n : ℕ) : Valid (state n).1 (state n).2 := by
  induction n with
  | zero => norm_num [state, Valid]
  | succ n ih =>
    rw [state_succ]
    exact step_valid ih

lemma state_growth (n : ℕ) : 8 * 2 ^ n ≤ (state n).1 := by
  induction n with
  | zero => norm_num [state]
  | succ n ih =>
    have hd := (digit_spec (state_valid n)).1
    rw [state_succ]
    simp only [step, pow_succ]
    nlinarith

lemma remainder_pos (n : ℕ) : 0 < (state n).2 := by
  have h := state_valid n
  have ha := h.1
  have hA : (0 : ℚ) < (state n).1 := by exact_mod_cast (show 0 < (state n).1 by omega)
  exact (by positivity : (0 : ℚ) < 1 / (4 * ((state n).1 : ℚ))).trans_le h.2.1

lemma remainder_bound (n : ℕ) : (state n).2 ≤ (1 / 2 : ℚ) ^ n := by
  have hA : 2 ^ n ≤ (state n).1 := by have := state_growth n; omega
  have hA' : (2 : ℚ) ^ n ≤ (state n).1 := by exact_mod_cast hA
  calc
    (state n).2 ≤ 1 / ((state n).1 : ℚ) := (state_valid n).2.2
    _ ≤ 1 / (2 : ℚ) ^ n := one_div_le_one_div_of_le (by positivity) hA'
    _ = (1 / 2 : ℚ) ^ n := by rw [div_pow, one_pow]

noncomputable def denominator (n : ℕ) : ℕ := (state (n + 1)).1 - 1

lemma denominator_pos (n : ℕ) : 0 < denominator n := by
  have := (state_valid (n + 1)).1
  unfold denominator
  omega

lemma denominator_add_one (n : ℕ) : denominator n + 1 = (state (n + 1)).1 := by
  have := (state_valid (n + 1)).1
  unfold denominator
  omega

lemma bounded_shifted_multiplier (n : ℕ) :
    ∃ q : ℕ, 2 ≤ q ∧ q ≤ 6 ∧ denominator (n + 1) + 1 = q * (denominator n + 1) := by
  refine ⟨digit (state (n + 1)).1 (state (n + 1)).2,
    (digit_spec (state_valid (n + 1))).1,
    (digit_spec (state_valid (n + 1))).2.1, ?_⟩
  rw [denominator_add_one, denominator_add_one, state_succ (n + 1)]
  rfl

lemma shifted_chain (n : ℕ) : denominator n + 1 ∣ denominator (n + 1) + 1 := by
  obtain ⟨q, _, _, hq⟩ := bounded_shifted_multiplier n
  rw [hq]
  exact dvd_mul_left _ _

lemma ratio_between_consecutive_integers (n : ℕ) :
    ∃ q : ℕ, 2 ≤ q ∧ q ≤ 6 ∧
      (q : ℚ) < (denominator (n + 1) : ℚ) / denominator n ∧
      (denominator (n + 1) : ℚ) / denominator n < (q : ℚ) + 1 := by
  obtain ⟨q, hl, hu, he⟩ := bounded_shifted_multiplier n
  have hd : 7 ≤ denominator n := by
    have h := (state_valid (n + 1)).1
    unfold denominator
    omega
  have hd' : (7 : ℚ) ≤ denominator n := by exact_mod_cast hd
  have hl' : (2 : ℚ) ≤ q := by exact_mod_cast hl
  have hu' : (q : ℚ) ≤ 6 := by exact_mod_cast hu
  have he' : (denominator (n + 1) : ℚ) + 1 = q * ((denominator n : ℚ) + 1) := by
    exact_mod_cast he
  refine ⟨q, hl, hu, ?_, ?_⟩
  · apply (lt_div_iff₀ (by linarith : (0 : ℚ) < denominator n)).mpr
    nlinarith
  · apply (div_lt_iff₀ (by linarith : (0 : ℚ) < denominator n)).mpr
    nlinarith

lemma remainder_difference (n : ℕ) :
    (state n).2 - (state (n + 1)).2 = 1 / (denominator n : ℚ) := by
  have h := (state_valid (n + 1)).1
  rw [denominator, Nat.cast_sub (by omega : 1 ≤ (state (n + 1)).1), Nat.cast_one]
  rw [state_succ]
  simp only [step]
  ring

open Filter
open scoped Topology

lemma remainder_tendsto_zero :
    Tendsto (fun n => ((state n).2 : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero _ _ (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
  · intro n
    exact_mod_cast (remainder_pos n).le
  · intro n
    have h := (Rat.cast_le (K := ℝ)).2 (remainder_bound n)
    simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

lemma hasSum_reciprocals :
    HasSum (fun n : ℕ => 1 / (denominator n : ℝ)) (1 / 16 : ℝ) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity) _).mpr
  have he (n : ℕ) :
      (∑ k ∈ Finset.range n, 1 / (denominator k : ℝ)) =
        (1 / 16 : ℝ) - ((state n).2 : ℝ) := by
    have hd (k : ℕ) : (1 / (denominator k : ℝ)) =
        ((state k).2 : ℝ) - ((state (k + 1)).2 : ℝ) := by
      have h := congrArg (fun x : ℚ => (x : ℝ)) (remainder_difference k).symm
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_sub] using h
    simp_rw [hd]
    rw [Finset.sum_range_sub']
    norm_num [state]
  simp_rw [he]
  simpa using tendsto_const_nhds.sub remainder_tendsto_zero

/-- An auxiliary rational example, with bounded shifted multipliers. -/
theorem exists_rational_bounded_chain :
    ∃ d : ℕ → ℕ,
      (∀ n, 0 < d n) ∧
      (∀ n, ∃ q : ℕ, 2 ≤ q ∧ q ≤ 6 ∧ d (n + 1) + 1 = q * (d n + 1)) ∧
      (∑' n : ℕ, 1 / (d n : ℝ)) = (1 / 16 : ℝ) :=
  ⟨denominator, denominator_pos, bounded_shifted_multiplier, hasSum_reciprocals.tsum_eq⟩

#print axioms exists_rational_bounded_chain
#print axioms ratio_between_consecutive_integers

end BoundedMultiplierRational
