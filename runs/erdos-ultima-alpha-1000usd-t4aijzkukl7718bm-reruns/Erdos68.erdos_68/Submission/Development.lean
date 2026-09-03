import FormalConjecturesUtil

/-! Verified analytic bounds for the series in Erdős problem 68. -/

namespace Erdos68Development

noncomputable def term (n : ℕ) : ℝ := 1 / ((n + 2).factorial - 1 : ℝ)

lemma factorial_ge_two (n : ℕ) : (2 : ℝ) ≤ (n + 2).factorial := by
  have h := Nat.factorial_le (show 2 ≤ n + 2 by omega)
  norm_num at h
  exact_mod_cast h

lemma denom_pos (n : ℕ) : (0 : ℝ) < (n + 2).factorial - 1 := by
  linarith [factorial_ge_two n]

lemma term_pos (n : ℕ) : 0 < term n := one_div_pos.mpr (denom_pos n)

lemma denom_succ (n : ℕ) :
    ((n + 1 + 2).factorial : ℝ) - 1 =
      (n + 3) * ((n + 2).factorial - 1 : ℝ) + (n + 2) := by
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.factorial_succ]
  push_cast
  ring

lemma term_succ_lt (n : ℕ) : term (n + 1) < (1 / (n + 3 : ℝ)) * term n := by
  unfold term
  rw [div_mul_div_comm, one_mul, denom_succ]
  apply one_div_lt_one_div_of_lt
  · exact mul_pos (by positivity) (denom_pos n)
  · have : (0 : ℝ) < n + 2 := by positivity
    linarith

lemma term_succ_le_third (n : ℕ) : term (n + 1) ≤ (1 / 3 : ℝ) * term n := by
  apply (term_succ_lt n).le.trans
  exact mul_le_mul_of_nonneg_right
    (one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])) (term_pos n).le

lemma summable_term : Summable term := by
  apply summable_of_ratio_norm_eventually_le (r := (1 / 3 : ℝ)) (by norm_num)
  exact Filter.Eventually.of_forall fun n => by
    simpa only [Real.norm_eq_abs, abs_of_pos (term_pos _)] using term_succ_le_third n

lemma term_add_le (n k : ℕ) : term (n + k) ≤ term n * (1 / 3 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      term (n + (k + 1)) ≤ (1 / 3 : ℝ) * term (n + k) := by
        simpa only [Nat.add_assoc] using term_succ_le_third (n + k)
      _ ≤ (1 / 3 : ℝ) * (term n * (1 / 3 : ℝ) ^ k) := by gcongr
      _ = term n * (1 / 3 : ℝ) ^ (k + 1) := by ring

lemma tail_bounds (n : ℕ) :
    0 < (∑' k : ℕ, term (n + k)) ∧
      (∑' k : ℕ, term (n + k)) ≤ (3 / 2 : ℝ) * term n := by
  have hs : Summable (fun k => term (n + k)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff n).mpr summable_term
  constructor
  · exact hs.tsum_pos (fun k => (term_pos _).le) 0 (term_pos (n + 0))
  · have hg : Summable (fun k : ℕ => term n * (1 / 3 : ℝ) ^ k) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 3 : ℝ) < 1)).mul_left _
    calc
      (∑' k : ℕ, term (n + k)) ≤ ∑' k : ℕ, term n * (1 / 3 : ℝ) ^ k :=
        Summable.tsum_le_tsum (term_add_le n) hs hg
      _ = (3 / 2 : ℝ) * term n := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 3 : ℝ) < 1)]
        ring



lemma partial_sum_error (n : ℕ) :
    0 < (∑' k : ℕ, term k) - ∑ k ∈ Finset.range n, term k ∧
      (∑' k : ℕ, term k) - ∑ k ∈ Finset.range n, term k ≤
        (3 / 2 : ℝ) * term n := by
  have h := Summable.sum_add_tsum_nat_add n summable_term
  have ht := tail_bounds n
  simp only [Nat.add_comm n] at ht
  constructor <;> linarith [ht.1, ht.2]

lemma term_le_factorial (n : ℕ) : term n ≤ 2 / (n + 2).factorial := by
  unfold term
  apply (div_le_div_iff₀ (denom_pos n) (by positivity)).mpr
  linarith [factorial_ge_two n]

lemma scaled_partial_sum_error (n : ℕ) :
    0 < ((n + 1).factorial : ℝ) *
        ((∑' k : ℕ, term k) - ∑ k ∈ Finset.range n, term k) ∧
      ((n + 1).factorial : ℝ) *
        ((∑' k : ℕ, term k) - ∑ k ∈ Finset.range n, term k) ≤
        3 / (n + 2 : ℝ) := by
  have hf : (0 : ℝ) < (n + 1).factorial := by positivity
  have h := partial_sum_error n
  constructor
  · exact mul_pos hf h.1
  · calc
      ((n + 1).factorial : ℝ) *
          ((∑' k : ℕ, term k) - ∑ k ∈ Finset.range n, term k) ≤
          ((n + 1).factorial : ℝ) * (3 / (n + 2).factorial) := by
        apply mul_le_mul_of_nonneg_left _ hf.le
        have ht := term_le_factorial n
        simp only [div_eq_mul_inv] at ht ⊢
        linarith [h.2]
      _ = 3 / (n + 2 : ℝ) := by
        rw [Nat.factorial_succ (n + 1)]
        push_cast
        field_simp
        ring

lemma rational_forces_partial_sums (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) (n : ℕ) (hn : q.den ≤ n + 1) :
    ∃ z : ℤ,
      (z : ℝ) - 3 / (n + 2 : ℝ) ≤
        ((n + 1).factorial : ℝ) * ∑ k ∈ Finset.range n, term k ∧
      ((n + 1).factorial : ℝ) * ∑ k ∈ Finset.range n, term k < z := by
  obtain ⟨c, hc⟩ := Nat.dvd_factorial q.pos hn
  have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hi : ((n + 1).factorial : ℝ) * (∑' k : ℕ, term k) =
      (q.num * (c : ℤ) : ℤ) := by
    rw [hq, Rat.cast_def, hc]
    push_cast
    field_simp
  refine ⟨q.num * (c : ℤ), ?_, ?_⟩
  · have h := (scaled_partial_sum_error n).2
    rw [mul_sub, hi] at h
    linarith
  · have h := (scaled_partial_sum_error n).1
    rw [mul_sub, hi] at h
    linarith

lemma irrational_of_arithmetic_condition
    (h : ∀ N : ℕ, ∃ n ≥ N, ∀ z : ℤ,
      ¬ ((z : ℝ) - 3 / (n + 2 : ℝ) ≤
          ((n + 1).factorial : ℝ) * ∑ k ∈ Finset.range n, term k ∧
        ((n + 1).factorial : ℝ) * ∑ k ∈ Finset.range n, term k < z)) :
    Irrational (∑' k : ℕ, term k) := by
  intro ⟨q, hq⟩
  obtain ⟨n, hn, hns⟩ := h q.den
  obtain ⟨z, hz⟩ := rational_forces_partial_sums q hq.symm n (by omega)
  exact hns z hz


lemma sum_bounds :
    (5 / 4 : ℝ) < (∑' k : ℕ, term k) ∧ (∑' k : ℕ, term k) < 63 / 50 := by
  have h := partial_sum_error 4
  have hs : (∑ k ∈ Finset.range 4, term k) = (17132 / 13685 : ℝ) := by
    norm_num [Finset.sum_range_succ, term, Nat.factorial]
  have ht : term 4 = (1 / 719 : ℝ) := by norm_num [term, Nat.factorial]
  rw [hs, ht] at h
  constructor <;> linarith [h.1, h.2]

lemma sum_not_integer (z : ℤ) : (∑' k : ℕ, term k) ≠ z := by
  intro h
  obtain ⟨hlo, hhi⟩ := sum_bounds
  rw [h] at hlo hhi
  have h1 : (1 : ℝ) < z := by linarith
  have h2 : (z : ℝ) < 2 := by linarith
  have h1' : (1 : ℤ) < z := by exact_mod_cast h1
  have h2' : z < (2 : ℤ) := by exact_mod_cast h2
  omega

end Erdos68Development

namespace Erdos68Development

open Filter
open scoped Topology

/-- The scaled partial sums, represented by exact rational arithmetic. -/
def scaledSumQ (n : ℕ) : ℚ :=
  (n + 1).factorial * ∑ k ∈ Finset.range n, 1 / ((k + 2).factorial - 1 : ℚ)

def carry (n : ℕ) : ℤ :=
  ⌊scaledSumQ (n + 1)⌋ - (n + 2 : ℤ) * ⌊scaledSumQ n⌋

def upperApprox (n : ℕ) : ℚ :=
  ((⌊scaledSumQ n⌋ + 1 : ℤ) : ℚ) / (n + 1).factorial

lemma cast_scaledSumQ (n : ℕ) : (scaledSumQ n : ℝ) =
    ((n + 1).factorial : ℝ) * ∑ k ∈ Finset.range n, term k := by
  simp [scaledSumQ, term]

lemma scaledSumQ_succ (n : ℕ) :
    scaledSumQ (n + 1) = (n + 2) * scaledSumQ n + 1 +
      1 / ((n + 2).factorial - 1 : ℚ) := by
  have hf : ((n + 2).factorial - 1 : ℚ) ≠ 0 := by
    have : (2 : ℚ) ≤ (n + 2).factorial := by exact_mod_cast factorial_ge_two n
    linarith
  unfold scaledSumQ
  rw [Finset.sum_range_succ]
  have hid : ((n + 2).factorial : ℚ) * (1 / ((n + 2).factorial - 1 : ℚ)) =
      1 + 1 / ((n + 2).factorial - 1 : ℚ) := by
    field_simp
    ring
  rw [mul_add, hid, Nat.factorial_succ (n + 1)]
  push_cast
  ring

lemma upperApprox_error (n : ℕ) :
    0 ≤ (upperApprox n : ℝ) - ∑ k ∈ Finset.range n, term k ∧
      (upperApprox n : ℝ) - ∑ k ∈ Finset.range n, term k ≤
        1 / ((n + 1).factorial : ℝ) := by
  have hf : (0 : ℝ) < (n + 1).factorial := by positivity
  have hlo : (⌊scaledSumQ n⌋ : ℝ) ≤ (scaledSumQ n : ℝ) := by
    exact_mod_cast Int.floor_le (scaledSumQ n)
  have hhi : (scaledSumQ n : ℝ) < (⌊scaledSumQ n⌋ : ℝ) + 1 := by
    exact_mod_cast Int.lt_floor_add_one (scaledSumQ n)
  rw [cast_scaledSumQ] at hlo hhi
  have he : (upperApprox n : ℝ) - ∑ k ∈ Finset.range n, term k =
      ((⌊scaledSumQ n⌋ : ℝ) + 1 -
        ((n + 1).factorial : ℝ) * ∑ k ∈ Finset.range n, term k) / (n + 1).factorial := by
    simp only [upperApprox, Rat.cast_div, Int.cast_add,
      Int.cast_one, Rat.cast_natCast]
    field_simp
    push_cast
    ring
  rw [he]
  constructor
  · exact div_nonneg (by linarith) hf.le
  · exact div_le_div_of_nonneg_right (by linarith) hf.le

lemma tendsto_upperApprox : Tendsto (fun n => (upperApprox n : ℝ)) atTop
    (𝓝 (∑' k : ℕ, term k)) := by
  have hf : Tendsto (fun n => 1 / ((n + 1).factorial : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp
      (factorial_tendsto_atTop.comp (tendsto_add_atTop_nat 1))
  have he := squeeze_zero (fun n => (upperApprox_error n).1)
    (fun n => (upperApprox_error n).2) hf
  simpa only [sub_add_cancel, zero_add] using he.add summable_term.tendsto_sum_tsum_nat

lemma upperApprox_eventually_eq_of_rational (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) :
    ∀ᶠ n in atTop, upperApprox n = q := by
  apply eventually_atTop.mpr
  refine ⟨max 2 q.den, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hnq : q.den ≤ n + 1 := by omega
  obtain ⟨c, hc⟩ := Nat.dvd_factorial q.pos hnq
  have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hf : (0 : ℝ) < (n + 1).factorial := by positivity
  let z : ℤ := q.num * (c : ℤ)
  have hi : ((n + 1).factorial : ℝ) * (∑' k : ℕ, term k) = (z : ℝ) := by
    rw [hq, Rat.cast_def, hc]
    dsimp [z]
    push_cast
    field_simp
  have he := scaled_partial_sum_error n
  rw [mul_sub, hi] at he
  have hlt : (3 / (n + 2 : ℝ)) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have hfloor : ⌊scaledSumQ n⌋ = z - 1 := by
    rw [← Rat.floor_cast (α := ℝ), Int.floor_eq_iff, cast_scaledSumQ]
    push_cast
    constructor <;> linarith [he.1, he.2]
  apply Rat.cast_injective (α := ℝ)
  simp only [upperApprox, hfloor, sub_add_cancel, Rat.cast_div, Rat.cast_intCast,
    Rat.cast_natCast]
  apply (div_eq_iff (ne_of_gt hf)).mpr
  rw [hq] at hi
  linarith

lemma upperApprox_succ_eq_iff (n : ℕ) :
    upperApprox (n + 1) = upperApprox n ↔ carry n = (n + 1 : ℤ) := by
  have hf : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
  have hn : (n + 2 : ℚ) ≠ 0 := by positivity
  unfold upperApprox carry
  rw [Nat.factorial_succ (n + 1)]
  push_cast
  field_simp
  constructor
  · intro h
    have hh : (⌊scaledSumQ (n + 1)⌋ : ℚ) - (n + 2 : ℚ) * ⌊scaledSumQ n⌋ = (n + 1 : ℚ) := by
      nlinarith
    exact_mod_cast hh
  · intro h
    have hh : (⌊scaledSumQ (n + 1)⌋ : ℚ) - (n + 2 : ℚ) * ⌊scaledSumQ n⌋ = (n + 1 : ℚ) := by
      exact_mod_cast h
    nlinarith

lemma rational_of_carry_eventually
    (h : ∀ᶠ n in atTop, carry n = (n + 1 : ℤ)) :
    ∃ q : ℚ, (∑' k : ℕ, term k) = (q : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hu : ∀ k : ℕ, upperApprox (N + k) = upperApprox N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        upperApprox (N + (k + 1)) = upperApprox (N + k) := by
          simpa only [Nat.add_assoc] using
            (upperApprox_succ_eq_iff (N + k)).mpr (hN (N + k) (by omega))
        _ = upperApprox N := ih
  have he : ∀ᶠ n in atTop, (upperApprox n : ℝ) = (upperApprox N : ℝ) := by
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact congrArg (fun q : ℚ => (q : ℝ)) (hu k)
  have ht : Tendsto (fun n => (upperApprox n : ℝ)) atTop (𝓝 (upperApprox N : ℝ)) :=
    Filter.Tendsto.congr' (Filter.EventuallyEq.symm he) tendsto_const_nhds
  exact ⟨upperApprox N, tendsto_nhds_unique tendsto_upperApprox ht⟩

lemma irrational_iff_carry_not_eventually :
    Irrational (∑' k : ℕ, term k) ↔ ¬ ∀ᶠ n in atTop, carry n = (n + 1 : ℤ) := by
  constructor
  · intro hi hc
    obtain ⟨q, hq⟩ := rational_of_carry_eventually hc
    exact hi ⟨q, hq.symm⟩
  · intro hc ⟨q, hq⟩
    have he := upperApprox_eventually_eq_of_rational q hq.symm
    have he' : ∀ᶠ n in atTop, upperApprox (n + 1) = q :=
      (tendsto_add_atTop_nat 1).eventually he
    apply hc
    filter_upwards [he, he'] with n h0 h1
    exact (upperApprox_succ_eq_iff n).mp (h1.trans h0.symm)

/-- A purely finite-arithmetic reformulation of the original irrationality problem. -/
lemma irrational_iff_carry_changes :
    Irrational (∑' k : ℕ, term k) ↔
      ∀ N : ℕ, ∃ n ≥ N, carry n ≠ (n + 1 : ℤ) := by
  rw [irrational_iff_carry_not_eventually]
  simp only [eventually_atTop, not_exists, not_forall, exists_prop]

end Erdos68Development

namespace Erdos68Development

/-- Natural-number denominators of the original series. -/
def denom (n : ℕ) : ℕ := (n + 2).factorial - 1

lemma denom_nat_succ (n : ℕ) : denom (n + 1) = (n + 3) * denom n + (n + 2) := by
  have hf : 1 ≤ (n + 2).factorial := Nat.factorial_pos _
  have hm : n + 3 ≤ (n + 3) * (n + 2).factorial := by nlinarith
  unfold denom
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.factorial_succ,
    show n + 2 + 1 = n + 3 by omega, Nat.mul_sub_left_distrib]
  omega

lemma denom_consecutive_coprime (n : ℕ) : (denom n).Coprime (denom (n + 1)) := by
  rw [denom_nat_succ, Nat.coprime_mul_right_add_right]
  apply Nat.Coprime.symm
  have hc : ((n + 2).factorial).Coprime (denom n) :=
    (Nat.coprime_self_sub_right (show 1 ≤ (n + 2).factorial from Nat.factorial_pos _)).mpr
      (Nat.coprime_one_right _)
  exact hc.of_dvd_left (Nat.dvd_factorial (by omega) le_rfl)

lemma denom_ge_add_five {n : ℕ} (hn : 2 ≤ n) : n + 5 ≤ denom n := by
  have h2 : 2 ≤ (n + 1).factorial := by
    have := Nat.factorial_le (show 2 ≤ n + 1 by omega)
    norm_num at this
    exact this
  have hf : n + 6 ≤ (n + 2).factorial := by
    rw [Nat.factorial_succ (n + 1)]
    nlinarith
  unfold denom
  omega

lemma denom_product_gt_next {n : ℕ} (hn : 2 ≤ n) :
    denom (n + 2) < denom n * denom (n + 1) := by
  have h0 := denom_ge_add_five hn
  have h1 := denom_ge_add_five (show 2 ≤ n + 1 by omega)
  have h2 := denom_nat_succ (n + 1)
  have hm := Nat.mul_le_mul_right (denom (n + 1)) h0
  have he : n + 1 + 1 = n + 2 := by omega
  rw [he] at h2
  nlinarith

lemma clearing_multiplier_gt_next_denom {n M : ℕ} (hn : 2 ≤ n) (hM : 0 < M)
    (hd0 : denom n ∣ M) (hd1 : denom (n + 1) ∣ M) : denom (n + 2) < M := by
  have hd := (denom_consecutive_coprime n).mul_dvd_of_dvd_of_dvd hd0 hd1
  exact (denom_product_gt_next hn).trans_le (Nat.le_of_dvd hM hd)

lemma term_eq_inv_denom (n : ℕ) : term n = 1 / (denom n : ℝ) := by
  unfold term denom
  rw [Nat.cast_sub (show 1 ≤ (n + 2).factorial from Nat.factorial_pos _), Nat.cast_one]

lemma term_le_tail (n : ℕ) : term n ≤
    (∑' k : ℕ, term k) - ∑ k ∈ Finset.range n, term k := by
  have hs : Summable (fun k => term (k + n)) := (summable_nat_add_iff n).mpr summable_term
  have hl := hs.le_tsum 0 (fun k _ => (term_pos _).le)
  have he := Summable.sum_add_tsum_nat_add n summable_term
  simp only [zero_add] at hl
  linarith

/-- Clearing even the last two denominators makes the remaining scaled tail exceed one.
Thus the direct termwise-denominator-clearing proof used for `e` cannot work here. -/
lemma termwise_clearing_tail_gt_one {n M : ℕ} (hn : 2 ≤ n) (hM : 0 < M)
    (hd0 : denom n ∣ M) (hd1 : denom (n + 1) ∣ M) :
    1 < (M : ℝ) *
      ((∑' k : ℕ, term k) - ∑ k ∈ Finset.range (n + 2), term k) := by
  have hd : (0 : ℝ) < denom (n + 2) := by
    have : 0 < denom (n + 2) := by
      have := denom_ge_add_five (show 2 ≤ n + 2 by omega)
      omega
    exact_mod_cast this
  have hm : (denom (n + 2) : ℝ) < M := by
    exact_mod_cast clearing_multiplier_gt_next_denom hn hM hd0 hd1
  have ht : (1 : ℝ) < M * term (n + 2) := by
    rw [term_eq_inv_denom, mul_one_div, one_lt_div hd]
    exact hm
  exact ht.trans_le (mul_le_mul_of_nonneg_left (term_le_tail (n + 2)) (by positivity))

end Erdos68Development

namespace Erdos68Development

noncomputable def correction (n : ℕ) : ℝ :=
  1 / (((n + 2).factorial : ℝ) * ((n + 2).factorial - 1))

lemma correction_pos (n : ℕ) : 0 < correction n := by
  exact one_div_pos.mpr (mul_pos (by positivity) (denom_pos n))

lemma term_split (n : ℕ) :
    term n = 1 / ((n + 2).factorial : ℝ) + correction n := by
  have hf : ((n + 2).factorial : ℝ) ≠ 0 := by positivity
  have hd := (denom_pos n).ne'
  unfold term correction
  field_simp
  ring

lemma summable_reciprocal_factorial :
    Summable (fun n : ℕ => 1 / ((n + 2).factorial : ℝ)) := by
  have hs : Summable (fun n : ℕ => 1 / (n.factorial : ℝ)) := by
    simpa only [one_pow] using Real.summable_pow_div_factorial 1
  exact (summable_nat_add_iff 2).mpr hs

lemma summable_correction : Summable correction := by
  have hs := summable_term.sub summable_reciprocal_factorial
  convert hs using 1
  ext n
  have := term_split n
  linarith

lemma reciprocal_factorial_sum :
    (∑' n : ℕ, 1 / ((n + 2).factorial : ℝ)) = Real.exp 1 - 2 := by
  have he : HasSum (fun n : ℕ => 1 / (n.factorial : ℝ)) (Real.exp 1) := by
    simpa only [one_pow, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (1 : ℝ))
  have h := he.summable.sum_add_tsum_nat_add 2
  rw [he.tsum_eq] at h
  norm_num [Finset.sum_range_succ] at h
  simp only [one_div]
  linarith

/-- The factorial-denominator series is `e - 2` plus a positive correction. -/
lemma sum_eq_exp_add_correction :
    (∑' n : ℕ, term n) = Real.exp 1 - 2 + ∑' n : ℕ, correction n := by
  simp_rw [term_split]
  rw [summable_reciprocal_factorial.tsum_add summable_correction,
    reciprocal_factorial_sum]

lemma correction_succ_le (n : ℕ) :
    correction (n + 1) ≤ (1 / 9 : ℝ) * correction n := by
  have he (k : ℕ) : correction k = term k / (k + 2).factorial := by
    unfold correction term
    rw [div_div]
    ring
  rw [he (n + 1), he n,
    show n + 1 + 2 = (n + 2) + 1 by omega, Nat.factorial_succ]
  push_cast
  have hf : (0 : ℝ) < (n + 2).factorial := by positivity
  have hn : (0 : ℝ) < n + 2 + 1 := by positivity
  apply (div_le_iff₀ (mul_pos hn hf)).mpr
  have h1 := term_succ_le_third n
  have h2 : (0 : ℝ) ≤ term n := (term_pos n).le
  have hh : (1 / 3 : ℝ) * term n ≤
      (1 / 9 : ℝ) * (term n / (n + 2).factorial) *
        ((n + 2 + 1) * (n + 2).factorial) := by
    field_simp
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact h1.trans hh

end Erdos68Development

namespace Erdos68Development

lemma correction_add_le (n k : ℕ) :
    correction (n + k) ≤ correction n * (1 / 9 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      correction (n + (k + 1)) ≤ (1 / 9 : ℝ) * correction (n + k) := by
        simpa only [Nat.add_assoc] using correction_succ_le (n + k)
      _ ≤ (1 / 9 : ℝ) * (correction n * (1 / 9 : ℝ) ^ k) := by gcongr
      _ = correction n * (1 / 9 : ℝ) ^ (k + 1) := by ring

lemma correction_tail_bounds (n : ℕ) :
    0 < (∑' k : ℕ, correction (n + k)) ∧
      (∑' k : ℕ, correction (n + k)) ≤ (9 / 8 : ℝ) * correction n := by
  have hs : Summable (fun k => correction (n + k)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff n).mpr summable_correction
  constructor
  · exact hs.tsum_pos (fun k => (correction_pos _).le) 0 (correction_pos (n + 0))
  · have hg : Summable (fun k : ℕ => correction n * (1 / 9 : ℝ) ^ k) :=
      (summable_geometric_of_lt_one (by norm_num)
        (by norm_num : (1 / 9 : ℝ) < 1)).mul_left _
    calc
      (∑' k : ℕ, correction (n + k)) ≤
          ∑' k : ℕ, correction n * (1 / 9 : ℝ) ^ k :=
        Summable.tsum_le_tsum (correction_add_le n) hs hg
      _ = (9 / 8 : ℝ) * correction n := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num)
          (by norm_num : (1 / 9 : ℝ) < 1)]
        ring

lemma correction_partial_sum_error (n : ℕ) :
    0 < (∑' k : ℕ, correction k) - ∑ k ∈ Finset.range n, correction k ∧
      (∑' k : ℕ, correction k) - ∑ k ∈ Finset.range n, correction k ≤
        (9 / 8 : ℝ) * correction n := by
  have h := Summable.sum_add_tsum_nat_add n summable_correction
  have ht := correction_tail_bounds n
  simp only [Nat.add_comm n] at ht
  constructor <;> linarith [ht.1, ht.2]

/-- Under the conjectured sum's rationality, the correction partial sums give
rational upper approximations to `exp 1`. No denominator bound is claimed. -/
lemma rational_sum_forces_exp_approximations (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) (n : ℕ) :
    0 < (q : ℝ) + 2 - ∑ k ∈ Finset.range n, correction k - Real.exp 1 ∧
      (q : ℝ) + 2 - ∑ k ∈ Finset.range n, correction k - Real.exp 1 ≤
        (9 / 8 : ℝ) * correction n := by
  have h := sum_eq_exp_add_correction
  rw [hq] at h
  have he := correction_partial_sum_error n
  constructor <;> linarith [he.1, he.2]

end Erdos68Development

namespace Erdos68Development

/-- The fixed-power factorial series in the geometric expansion of `term`. -/
noncomputable def powerTerm (r n : ℕ) : ℝ :=
  1 / (((n + 2).factorial : ℝ) ^ (r + 1))

lemma powerTerm_pos (r n : ℕ) : 0 < powerTerm r n := by
  unfold powerTerm
  positivity

lemma powerTerm_succ (r n : ℕ) :
    powerTerm r (n + 1) = (1 / (n + 3 : ℝ)) ^ (r + 1) * powerTerm r n := by
  unfold powerTerm
  rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.factorial_succ]
  push_cast
  rw [mul_pow]
  simp only [one_div, mul_inv, inv_pow]
  congr 2
  ring

lemma powerTerm_succ_le_third (r n : ℕ) :
    powerTerm r (n + 1) ≤ (1 / 3 : ℝ) * powerTerm r n := by
  rw [powerTerm_succ]
  apply mul_le_mul_of_nonneg_right _ (powerTerm_pos r n).le
  have h0 : (0 : ℝ) ≤ 1 / (n + 3 : ℝ) := by positivity
  have h1 : 1 / (n + 3 : ℝ) ≤ (1 / 3 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [Nat.cast_nonneg (α := ℝ) n]
  calc
    (1 / (n + 3 : ℝ)) ^ (r + 1) =
        (1 / (n + 3 : ℝ)) ^ r * (1 / (n + 3 : ℝ)) := pow_succ _ _
    _ ≤ 1 * (1 / (n + 3 : ℝ)) :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ h0 (h1.trans (by norm_num))) h0
    _ ≤ 1 / 3 := by simpa using h1

lemma summable_powerTerm (r : ℕ) : Summable (powerTerm r) := by
  apply summable_of_ratio_norm_eventually_le (r := (1 / 3 : ℝ)) (by norm_num)
  exact Filter.Eventually.of_forall fun n => by
    simpa only [Real.norm_eq_abs, abs_of_pos (powerTerm_pos _ _)] using
      powerTerm_succ_le_third r n

lemma powerTerm_add_le (r n k : ℕ) :
    powerTerm r (n + k) ≤ powerTerm r n * (1 / 3 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      powerTerm r (n + (k + 1)) ≤ (1 / 3 : ℝ) * powerTerm r (n + k) := by
        simpa only [Nat.add_assoc] using powerTerm_succ_le_third r (n + k)
      _ ≤ (1 / 3 : ℝ) * (powerTerm r n * (1 / 3 : ℝ) ^ k) := by gcongr
      _ = powerTerm r n * (1 / 3 : ℝ) ^ (k + 1) := by ring

lemma powerTerm_tail_bounds (r n : ℕ) :
    0 < (∑' k : ℕ, powerTerm r (n + k)) ∧
      (∑' k : ℕ, powerTerm r (n + k)) ≤ (3 / 2 : ℝ) * powerTerm r n := by
  have hs : Summable (fun k => powerTerm r (n + k)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff n).mpr (summable_powerTerm r)
  constructor
  · exact hs.tsum_pos (fun k => (powerTerm_pos _ _).le) 0 (powerTerm_pos r (n + 0))
  · have hg : Summable (fun k : ℕ => powerTerm r n * (1 / 3 : ℝ) ^ k) :=
      (summable_geometric_of_lt_one (by norm_num)
        (by norm_num : (1 / 3 : ℝ) < 1)).mul_left _
    calc
      (∑' k : ℕ, powerTerm r (n + k)) ≤
          ∑' k : ℕ, powerTerm r n * (1 / 3 : ℝ) ^ k :=
        Summable.tsum_le_tsum (powerTerm_add_le r n) hs hg
      _ = (3 / 2 : ℝ) * powerTerm r n := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num)
          (by norm_num : (1 / 3 : ℝ) < 1)]
        ring

lemma powerTerm_partial_sum_error (r n : ℕ) :
    0 < (∑' k : ℕ, powerTerm r k) - ∑ k ∈ Finset.range n, powerTerm r k ∧
      (∑' k : ℕ, powerTerm r k) - ∑ k ∈ Finset.range n, powerTerm r k ≤
        (3 / 2 : ℝ) * powerTerm r n := by
  have h := Summable.sum_add_tsum_nat_add n (summable_powerTerm r)
  have ht := powerTerm_tail_bounds r n
  simp only [Nat.add_comm n] at ht
  constructor <;> linarith [ht.1, ht.2]

end Erdos68Development

namespace Erdos68Development

lemma scaled_powerTerm_error (r n : ℕ) :
    0 < ((n + 1).factorial : ℝ) ^ (r + 1) *
        ((∑' k : ℕ, powerTerm r k) - ∑ k ∈ Finset.range n, powerTerm r k) ∧
      ((n + 1).factorial : ℝ) ^ (r + 1) *
        ((∑' k : ℕ, powerTerm r k) - ∑ k ∈ Finset.range n, powerTerm r k) < 1 := by
  have hf : (0 : ℝ) < ((n + 1).factorial : ℝ) ^ (r + 1) := by positivity
  have he := powerTerm_partial_sum_error r n
  have hs : ((n + 1).factorial : ℝ) ^ (r + 1) * powerTerm r n =
      (1 / (n + 2 : ℝ)) ^ (r + 1) := by
    unfold powerTerm
    rw [Nat.factorial_succ (n + 1)]
    push_cast
    rw [mul_pow]
    simp only [one_div, inv_pow]
    field_simp
    congr 1
    ring
  have h0 : (0 : ℝ) ≤ 1 / (n + 2 : ℝ) := by positivity
  have h1 : 1 / (n + 2 : ℝ) ≤ (1 / 2 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hp : (1 / (n + 2 : ℝ)) ^ (r + 1) ≤ (1 / 2 : ℝ) := by
    calc
      (1 / (n + 2 : ℝ)) ^ (r + 1) =
          (1 / (n + 2 : ℝ)) ^ r * (1 / (n + 2 : ℝ)) := pow_succ _ _
      _ ≤ 1 * (1 / (n + 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ h0 (h1.trans (by norm_num))) h0
      _ ≤ 1 / 2 := by simpa using h1
  constructor
  · exact mul_pos hf he.1
  · have h := mul_le_mul_of_nonneg_left he.2 hf.le
    have hh : ((n + 1).factorial : ℝ) ^ (r + 1) *
        ((3 / 2 : ℝ) * powerTerm r n) ≤ (3 / 4 : ℝ) := by
      calc
        _ = (3 / 2 : ℝ) *
            (((n + 1).factorial : ℝ) ^ (r + 1) * powerTerm r n) := by ring
        _ = (3 / 2 : ℝ) * (1 / (n + 2 : ℝ)) ^ (r + 1) := by rw [hs]
        _ ≤ 3 / 4 := by linarith
    linarith

lemma powerTerm_partial_sum_integral (r n : ℕ) :
    ∃ z : ℕ, ((n + 1).factorial : ℝ) ^ (r + 1) *
      (∑ k ∈ Finset.range n, powerTerm r k) = z := by
  refine ⟨∑ k ∈ Finset.range n,
    (n + 1).factorial ^ (r + 1) / (k + 2).factorial ^ (r + 1), ?_⟩
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k + 2 ≤ n + 1 := by
    have := Finset.mem_range.mp hk
    omega
  have hd : (k + 2).factorial ^ (r + 1) ∣ (n + 1).factorial ^ (r + 1) :=
    pow_dvd_pow_of_dvd (Nat.factorial_dvd_factorial hk') _
  rw [Nat.cast_div_charZero hd]
  simp [powerTerm, div_eq_mul_inv]

/-- Every fixed positive power of the reciprocal-factorial series is irrational.
This does not assert that an infinite sum of these irrational values is irrational. -/
lemma irrational_sum_powerTerm (r : ℕ) : Irrational (∑' k : ℕ, powerTerm r k) := by
  intro ⟨q, hq⟩
  let n := q.den
  have hd : q.den ∣ (n + 1).factorial ^ (r + 1) :=
    (Nat.dvd_factorial q.pos (by dsimp [n]; omega)).trans
      (dvd_pow_self _ (by omega))
  obtain ⟨c, hc⟩ := hd
  obtain ⟨z, hz⟩ := powerTerm_partial_sum_integral r n
  have hd0 : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hi : ((n + 1).factorial : ℝ) ^ (r + 1) *
      (∑' k : ℕ, powerTerm r k) = (q.num * (c : ℤ) : ℤ) := by
    rw [← hq, Rat.cast_def]
    have hc' : ((n + 1).factorial : ℝ) ^ (r + 1) = (q.den : ℝ) * c := by
      exact_mod_cast hc
    rw [hc']
    push_cast
    field_simp
  have he := scaled_powerTerm_error r n
  rw [mul_sub, hi, hz] at he
  push_cast at he
  have h0 : (0 : ℝ) < ((q.num * (c : ℤ) - (z : ℤ) : ℤ) : ℝ) := by
    push_cast
    exact he.1
  have h1 : ((q.num * (c : ℤ) - (z : ℤ) : ℤ) : ℝ) < 1 := by
    push_cast
    exact he.2
  have h0' : (0 : ℤ) < q.num * (c : ℤ) - (z : ℤ) := by exact_mod_cast h0
  have h1' : q.num * (c : ℤ) - (z : ℤ) < (1 : ℤ) := by exact_mod_cast h1
  omega

end Erdos68Development

namespace Erdos68Development

lemma powerTerm_eq_geometric (r n : ℕ) :
    powerTerm r n = (1 / ((n + 2).factorial : ℝ)) ^ r *
      (1 / ((n + 2).factorial : ℝ)) := by
  simp [powerTerm, pow_succ, one_div, inv_pow, mul_comm]

lemma reciprocal_factorial_lt_one (n : ℕ) :
    (1 / ((n + 2).factorial : ℝ)) < 1 := by
  apply (div_lt_one (by positivity)).mpr
  linarith [factorial_ge_two n]

lemma summable_powerTerm_orders (n : ℕ) :
    Summable (fun r : ℕ => powerTerm r n) := by
  simp_rw [powerTerm_eq_geometric]
  exact (summable_geometric_of_lt_one (by positivity)
    (reciprocal_factorial_lt_one n)).mul_right _

lemma sum_powerTerm_orders (n : ℕ) :
    (∑' r : ℕ, powerTerm r n) = term n := by
  simp_rw [powerTerm_eq_geometric]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by positivity)
    (reciprocal_factorial_lt_one n)]
  have hf : ((n + 2).factorial : ℝ) ≠ 0 := by positivity
  have hd := (denom_pos n).ne'
  unfold term
  field_simp

lemma summable_powerTerm_pairs :
    Summable (fun p : ℕ × ℕ => powerTerm p.2 p.1) := by
  apply (summable_prod_of_nonneg (fun p => (powerTerm_pos p.2 p.1).le)).mpr
  refine ⟨summable_powerTerm_orders, ?_⟩
  simpa only [sum_powerTerm_orders] using summable_term

lemma summable_powerSums : Summable (fun r : ℕ => ∑' n : ℕ, powerTerm r n) :=
  summable_powerTerm_pairs.prod_symm.prod

/-- The original sum is an infinite sum of irrational factorial-power sums.
No irrationality claim about the outer sum follows from this identity alone. -/
lemma sum_eq_sum_powerSums :
    (∑' n : ℕ, term n) = ∑' r : ℕ, ∑' n : ℕ, powerTerm r n := by
  have h : (∑' r : ℕ, ∑' n : ℕ, powerTerm r n) =
      ∑' n : ℕ, ∑' r : ℕ, powerTerm r n :=
    Summable.tsum_comm (f := fun n r : ℕ => powerTerm r n) summable_powerTerm_pairs
  simpa only [sum_powerTerm_orders] using h.symm

end Erdos68Development

namespace Erdos68Development

open Filter
open scoped Topology

/-- The denominators of the rational upper approximants tend to infinity
exactly when the original series is irrational. The denominator growth is
not established by this equivalence. -/
lemma irrational_iff_upperApprox_den_tendsto :
    Irrational (∑' k : ℕ, term k) ↔
      Tendsto (fun n => (upperApprox n).den) atTop atTop := by
  constructor
  · intro hi
    apply tendsto_atTop.mpr
    intro B
    have hd : Tendsto (fun n => dist (∑' k : ℕ, term k) (upperApprox n : ℝ))
        atTop (𝓝 0) := by
      simpa only [dist_self] using
        (tendsto_const_nhds (x := (∑' k : ℕ, term k))).dist tendsto_upperApprox
    have h2 : Tendsto (fun n => (2 : ℝ) *
        dist (∑' k : ℕ, term k) (upperApprox n : ℝ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hd
    have he := h2.eventually (hi.eventually_forall_le_dist_cast_rat_of_den_le B)
    filter_upwards [he] with n hn
    by_contra h
    have hl := hn (upperApprox n) (by omega)
    have hp : 0 < dist (∑' k : ℕ, term k) (upperApprox n : ℝ) :=
      dist_pos.mpr (hi.ne_rat (upperApprox n))
    linarith
  · intro hd ⟨q, hq⟩
    have h1 := upperApprox_eventually_eq_of_rational q hq.symm
    have h2 := (tendsto_atTop.mp hd) (q.den + 1)
    obtain ⟨n, hn, hn'⟩ := (h1.and h2).exists
    rw [hn] at hn'
    omega

/-- A concrete decrease rules out proving denominator growth by monotonicity. -/
lemma upperApprox_den_decrease : (upperApprox 10).den < (upperApprox 9).den := by
  norm_num [upperApprox, scaledSumQ, Finset.sum_range_succ, Nat.factorial]

lemma upperApprox_den_not_monotone : ¬ Monotone (fun n => (upperApprox n).den) := by
  intro h
  exact (not_le_of_gt upperApprox_den_decrease) (h (by decide : 9 ≤ 10))

end Erdos68Development

namespace Erdos68Development

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- A constancy carry really occurs: excluding it at every index would be false. -/
lemma carry_fifty : carry 50 = (51 : ℤ) := by
  norm_num [carry, scaledSumQ, Finset.sum_range_succ, Nat.factorial]

lemma not_forall_carry_changes :
    ¬ (∀ n : ℕ, carry n ≠ (n + 1 : ℤ)) := by
  intro h
  exact h 50 (by norm_num [carry_fifty])

end Erdos68Development



namespace Erdos68Development

lemma upperApprox_backward {n : ℕ} (hn : 1 ≤ n) (z : ℤ)
    (hz : upperApprox (n + 1) = (z : ℚ) / (n + 1).factorial) :
    upperApprox n = (z : ℚ) / (n + 1).factorial := by
  have hf : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
  have hnpos : (0 : ℚ) < n + 2 := by positivity
  have hd : (2 : ℚ) ≤ (n + 2).factorial := by
    exact_mod_cast factorial_ge_two n
  have hδpos : (0 : ℚ) < 1 / ((n + 2).factorial - 1 : ℚ) :=
    one_div_pos.mpr (by linarith)
  have hδle : 1 / ((n + 2).factorial - 1 : ℚ) ≤ (1 : ℚ) := by
    apply (div_le_one (by linarith)).mpr
    linarith
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hnum : (⌊scaledSumQ (n + 1)⌋ : ℚ) + 1 = (n + 2 : ℚ) * z := by
    unfold upperApprox at hz
    rw [Nat.factorial_succ (n + 1)] at hz
    push_cast at hz
    field_simp [hf] at hz
    nlinarith
  have hlo := Int.floor_le (scaledSumQ (n + 1))
  have hhi := Int.lt_floor_add_one (scaledSumQ (n + 1))
  have hr := scaledSumQ_succ n
  have hfloor : ⌊scaledSumQ n⌋ = z - 1 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor
    · apply (mul_le_mul_iff_right₀ hnpos).mp
      nlinarith
    · apply (mul_lt_mul_iff_right₀ hnpos).mp
      nlinarith
  simp [upperApprox, hfloor]

lemma upperApprox_factorial_rep {i n : ℕ} (hin : i ≤ n) :
    ∃ z : ℤ, upperApprox i = (z : ℚ) / (n + 1).factorial := by
  obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial (Nat.add_le_add_right hin 1)
  refine ⟨(⌊scaledSumQ i⌋ + 1) * (c : ℤ), ?_⟩
  apply (eq_div_iff (by positivity : ((n + 1).factorial : ℚ) ≠ 0)).mpr
  unfold upperApprox
  rw [hc]
  push_cast
  field_simp

lemma upperApprox_no_return {i j k : ℕ} (hi : 1 ≤ i)
    (hij : i ≤ j) (hjk : j ≤ k) (hik : upperApprox k = upperApprox i) :
    upperApprox j = upperApprox i := by
  revert hik
  induction k, hjk using Nat.le_induction with
  | base => exact fun h => h
  | succ k hk ih =>
    intro h
    obtain ⟨z, hz⟩ := upperApprox_factorial_rep (hij.trans hk)
    apply ih
    exact (upperApprox_backward (by omega : 1 ≤ k) z (h.trans hz)).trans hz.symm

lemma upperApprox_change_excludes_return {n m : ℕ} (hn : 1 ≤ n)
    (hm : n + 1 ≤ m) (hchange : upperApprox (n + 1) ≠ upperApprox n) :
    upperApprox m ≠ upperApprox n := by
  intro h
  exact hchange (upperApprox_no_return hn (by omega) hm h)

end Erdos68Development
