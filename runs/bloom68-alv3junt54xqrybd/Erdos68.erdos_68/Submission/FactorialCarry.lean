import Mathlib

/-!
# A conditional factorial-carry criterion for the factorial-minus-one series

This supporting module proves tail bounds and conditional criteria only.
In particular, it does **not** assert
that the fractional parts escape the corridor for arbitrarily large indices.

The terms at indices 0 and 1 in `factorialTerm` vanish (division by zero in a
field is zero), so `finitePrefix N` is exactly the finite sum over `2 ≤ n ≤ N`.
-/

namespace FactorialCarryCriterion

open Filter Topology

noncomputable def factorialTerm (n : ℕ) : ℝ :=
  1 / ((n.factorial : ℝ) - 1)

noncomputable def S : ℝ := ∑' n : ℕ, factorialTerm (n + 2)

noncomputable def finitePrefix (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), factorialTerm n

/-- The tail over factorial indices strictly greater than `N`. -/
noncomputable def tail (N : ℕ) : ℝ :=
  ∑' k : ℕ, factorialTerm (k + (N + 1))

noncomputable def scaledPrefix (N : ℕ) : ℝ :=
  (N.factorial : ℝ) * finitePrefix N

noncomputable def scaledTail (N : ℕ) : ℝ :=
  (N.factorial : ℝ) * tail N

/-- The integer immediately above the factorial-scaled finite prefix. -/
noncomputable def carry (N : ℕ) : ℤ := ⌊scaledPrefix N⌋ + 1

/-- The open corridor forced by rationality, for all sufficiently large `N`. -/
def Corridor (N : ℕ) : Prop :=
  Int.fract (scaledPrefix N) ∈
    Set.Ioo (1 - 1 / (N : ℝ)) (1 - 1 / ((N : ℝ) + 1))

lemma factorial_ge_two (n : ℕ) (hn : 2 ≤ n) :
    (2 : ℝ) ≤ (n.factorial : ℝ) := by
  exact_mod_cast (show 2 ≤ n.factorial from
    (by simpa using Nat.factorial_le hn))

lemma factorialTerm_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < factorialTerm n := by
  unfold factorialTerm
  exact one_div_pos.mpr (by linarith [factorial_ge_two n hn])

lemma factorialTerm_nonneg (n : ℕ) : 0 ≤ factorialTerm n := by
  by_cases hn : 2 ≤ n
  · exact (factorialTerm_pos n hn).le
  · have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> norm_num [factorialTerm]

lemma shiftedTerm_le_two_div_factorial (n : ℕ) :
    factorialTerm (n + 2) ≤ 2 / ((n + 2).factorial : ℝ) := by
  unfold factorialTerm
  have h := factorial_ge_two (n + 2) (by omega)
  apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < (n + 2).factorial - 1)
    (by linarith : (0 : ℝ) < (n + 2).factorial)).2
  linarith

lemma summable_shiftedTerm : Summable (fun n : ℕ => factorialTerm (n + 2)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / (n + 2).factorial) := by
    simpa using (summable_nat_add_iff 2).2 (Real.summable_pow_div_factorial 1)
  apply Summable.of_nonneg_of_le
    (fun n => factorialTerm_nonneg (n + 2)) shiftedTerm_le_two_div_factorial
  convert h.mul_left 2 using 1
  ext n
  ring

lemma summable_factorialTerm : Summable factorialTerm :=
  (summable_nat_add_iff 2).1 summable_shiftedTerm

lemma S_eq_tsum_factorialTerm : S = ∑' n : ℕ, factorialTerm n := by
  have h := summable_factorialTerm.sum_add_tsum_nat_add 2
  simpa [S, factorialTerm, Finset.sum_range_succ] using h

lemma prefix_eq_sum_Icc (N : ℕ) :
    finitePrefix N = ∑ n ∈ Finset.Icc 2 N, factorialTerm n := by
  unfold finitePrefix
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range]
    omega
  · intro n hn hn'
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Icc, not_and] at hn'
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> norm_num [factorialTerm]

lemma S_eq_prefix_add_tail (N : ℕ) : S = finitePrefix N + tail N := by
  rw [S_eq_tsum_factorialTerm]
  exact (summable_factorialTerm.sum_add_tsum_nat_add (N + 1)).symm

lemma scaled_decomposition (N : ℕ) :
    (N.factorial : ℝ) * S = scaledPrefix N + scaledTail N := by
  rw [S_eq_prefix_add_tail N]
  exact mul_add _ _ _

lemma prefix_succ (N : ℕ) :
    finitePrefix (N + 1) = finitePrefix N + factorialTerm (N + 1) := by
  exact Finset.sum_range_succ _ (N + 1)

lemma factorialTerm_step_lt (n : ℕ) (hn : 2 ≤ n) :
    factorialTerm (n + 1) < (1 / ((n : ℝ) + 1)) * factorialTerm n := by
  unfold factorialTerm
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    one_div_mul_one_div]
  apply one_div_lt_one_div_of_lt
  · exact mul_pos (by positivity) (by linarith [factorial_ge_two n hn])
  · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

lemma factorialTerm_step_le_uniform (M i : ℕ) (hM : 2 ≤ M) :
    factorialTerm (i + M + 1) ≤
      (1 / ((M : ℝ) + 1)) * factorialTerm (i + M) := by
  apply (factorialTerm_step_lt (i + M) (by omega)).le.trans
  apply mul_le_mul_of_nonneg_right _ (factorialTerm_nonneg (i + M))
  apply one_div_le_one_div_of_le (by positivity)
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) i]

lemma factorialTerm_le_geometric (M i : ℕ) (hM : 2 ≤ M) :
    factorialTerm (i + M) ≤
      (1 / ((M : ℝ) + 1)) ^ i * factorialTerm M := by
  have h := le_geom (u := fun n => factorialTerm (n + M))
    (c := 1 / ((M : ℝ) + 1)) (by positivity) i
    (fun n _ => by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      factorialTerm_step_le_uniform M n hM)
  simpa using h

/-- Strict geometric bounds for any tail starting at factorial index `M ≥ 2`. -/
lemma tail_geometric_bounds (M : ℕ) (hM : 2 ≤ M) :
    factorialTerm M < (∑' i : ℕ, factorialTerm (i + M)) ∧
      (∑' i : ℕ, factorialTerm (i + M)) <
        factorialTerm M / (1 - 1 / ((M : ℝ) + 1)) := by
  have hs : Summable (fun i => factorialTerm (i + M)) :=
    (summable_nat_add_iff M).2 summable_factorialTerm
  have hr0 : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
  have hr1 : 1 / ((M : ℝ) + 1) < 1 := by
    apply (div_lt_one (by positivity)).2
    have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hgeom := summable_geometric_of_lt_one hr0 hr1
  constructor
  · rw [hs.tsum_eq_zero_add]
    simp only [zero_add, lt_add_iff_pos_right]
    have hs' : Summable (fun i => factorialTerm (i + 1 + M)) := by
      simpa only [Nat.add_assoc] using
        (summable_nat_add_iff (1 + M)).2 summable_factorialTerm
    exact hs'.tsum_pos (fun i => factorialTerm_nonneg _) 0
      (factorialTerm_pos _ (by omega))
  · calc
      (∑' i : ℕ, factorialTerm (i + M)) <
          ∑' i : ℕ, (1 / ((M : ℝ) + 1)) ^ i * factorialTerm M := by
        apply Summable.tsum_lt_tsum (i := 1)
          (fun i => factorialTerm_le_geometric M i hM)
          _ hs (hgeom.mul_right _)
        simpa only [pow_one, Nat.add_comm] using factorialTerm_step_lt M hM
      _ = factorialTerm M / (1 - 1 / ((M : ℝ) + 1)) := by
        rw [hgeom.tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1]
        ring

lemma inverse_factorial_lt_term (n : ℕ) (hn : 2 ≤ n) :
    1 / (n.factorial : ℝ) < factorialTerm n := by
  unfold factorialTerm
  exact one_div_lt_one_div_of_lt
    (by linarith [factorial_ge_two n hn]) (by linarith)

/-- The requested sharp bounds: `1/(N+1) < N! * tail(N) < 1/N`. -/
theorem scaled_tail_bounds (N : ℕ) (hN : 3 ≤ N) :
    1 / ((N : ℝ) + 1) < scaledTail N ∧
      scaledTail N < 1 / (N : ℝ) := by
  have hF : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hfac : ((N + 1).factorial : ℝ) =
      ((N : ℝ) + 1) * (N.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have ht := tail_geometric_bounds (N + 1) (by omega)
  change factorialTerm (N + 1) < tail N ∧
    tail N < factorialTerm (N + 1) / (1 - 1 / ((N + 1 : ℕ) + 1 : ℝ)) at ht
  constructor
  · calc
      1 / ((N : ℝ) + 1) =
          (N.factorial : ℝ) * (1 / ((N + 1).factorial : ℝ)) := by
        rw [hfac]
        field_simp
      _ < (N.factorial : ℝ) * factorialTerm (N + 1) :=
        mul_lt_mul_of_pos_left (inverse_factorial_lt_term _ (by omega)) hF
      _ < scaledTail N := mul_lt_mul_of_pos_left ht.1 hF
  · apply (mul_lt_mul_of_pos_left ht.2 hF).trans_le
    have hFbig : (N : ℝ) + 1 ≤ (N.factorial : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_factorial_self hN))
    have hd : 0 < ((N : ℝ) + 1) * (N.factorial : ℝ) - 1 := by
      nlinarith
    have hr : 1 - 1 / ((N : ℝ) + 2) =
        ((N : ℝ) + 1) / ((N : ℝ) + 2) := by
      field_simp
      ring
    unfold factorialTerm
    rw [hfac]
    push_cast
    rw [show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring, hr]
    calc
      (N.factorial : ℝ) *
          (1 / (((N : ℝ) + 1) * (N.factorial : ℝ) - 1) /
            (((N : ℝ) + 1) / ((N : ℝ) + 2))) =
          (N.factorial : ℝ) * ((N : ℝ) + 2) /
            ((((N : ℝ) + 1) * (N.factorial : ℝ) - 1) * ((N : ℝ) + 1)) := by
        field_simp
      _ ≤ 1 / (N : ℝ) := by
        apply (div_le_div_iff₀ (mul_pos hd (by linarith)) (by linarith)).2
        nlinarith

/-- Divisibility of the reduced denominator makes the factorial multiple integral. -/
lemma factorial_mul_rat_integral_of_dvd (q : ℚ) (N : ℕ) (hN : q.den ∣ N.factorial) :
    ∃ z : ℤ, (N.factorial : ℝ) * (q : ℝ) = (z : ℝ) := by
  obtain ⟨k, hk⟩ := hN
  refine ⟨(k : ℤ) * q.num, ?_⟩
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  rw [hk, Nat.cast_mul, Rat.cast_def, Int.cast_mul, Int.cast_natCast]
  field_simp

/-- Any rational number becomes integral after multiplication by `N!` once
`N` is at least its denominator. -/
lemma factorial_mul_rat_integral (q : ℚ) (N : ℕ) (hN : q.den ≤ N) :
    ∃ z : ℤ, (N.factorial : ℝ) * (q : ℝ) = (z : ℝ) :=
  factorial_mul_rat_integral_of_dvd q N (Nat.dvd_factorial q.den_pos hN)

lemma carry_cast (N : ℕ) :
    (carry N : ℝ) = scaledPrefix N + 1 - Int.fract (scaledPrefix N) := by
  simp only [carry, Int.cast_add, Int.cast_one, Int.fract]
  ring

/-- If the scaled whole sum is integral, its prefix has fractional part
exactly one minus the scaled tail. -/
lemma fract_eq_one_sub_scaled_tail (N : ℕ) (hN : 3 ≤ N)
    (hint : ∃ z : ℤ, (N.factorial : ℝ) * S = (z : ℝ)) :
    Int.fract (scaledPrefix N) = 1 - scaledTail N := by
  obtain ⟨z, hz⟩ := hint
  have ht := scaled_tail_bounds N hN
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : 0 < scaledTail N :=
    (by positivity : (0 : ℝ) < 1 / ((N : ℝ) + 1)).trans ht.1
  have h1 : scaledTail N < 1 := by
    apply ht.2.trans
    exact (div_lt_one (by linarith)).2 (by linarith)
  rw [scaled_decomposition N] at hz
  apply Int.fract_eq_iff.mpr
  refine ⟨by linarith, by linarith, z - 1, ?_⟩
  push_cast
  linarith

lemma carry_eq_of_integral_scaled_sum (N : ℕ) (hN : 3 ≤ N) (z : ℤ)
    (hz : (N.factorial : ℝ) * S = (z : ℝ)) : carry N = z := by
  apply Int.cast_injective (α := ℝ)
  rw [carry_cast, fract_eq_one_sub_scaled_tail N hN ⟨z, hz⟩]
  have h := scaled_decomposition N
  linarith

lemma corridor_of_integral_scaled_sum (N : ℕ) (hN : 3 ≤ N)
    (hint : ∃ z : ℤ, (N.factorial : ℝ) * S = (z : ℝ)) : Corridor N := by
  have ht := scaled_tail_bounds N hN
  unfold Corridor
  rw [fract_eq_one_sub_scaled_tail N hN hint]
  exact ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- Rationality forces the corridor at every `N ≥ max 3 q.den`. -/
theorem rational_implies_corridor (q : ℚ) (hq : S = (q : ℝ))
    (N : ℕ) (hN : 3 ≤ N) (hden : q.den ≤ N) : Corridor N := by
  apply corridor_of_integral_scaled_sum N hN
  simpa only [hq] using factorial_mul_rat_integral q N hden

/-- **Conditional criterion only.**  The escape hypothesis is not proved in
this file.  Escapes at arbitrarily large indices imply irrationality. -/
theorem irrational_of_arbitrarily_large_escapes
    (hescape : ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ ¬ Corridor N) : Irrational S := by
  rintro ⟨q, hq⟩
  obtain ⟨N, hMN, hnot⟩ := hescape (max q.den 3)
  exact hnot (rational_implies_corridor q hq.symm N
    ((le_max_right q.den 3).trans hMN) ((le_max_left q.den 3).trans hMN))

/-- The same conditional criterion, with the original series and the finite
prefix written out explicitly.  The hypothesis of arbitrarily large escapes
remains a separate, unproved requirement. -/
theorem irrational_series_of_arbitrarily_large_escapes
    (hescape : ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
      Int.fract ((N.factorial : ℝ) *
        (∑ n ∈ Finset.Icc 2 N, 1 / ((n.factorial : ℝ) - 1))) ∉
        Set.Ioo (1 - 1 / (N : ℝ)) (1 - 1 / ((N : ℝ) + 1))) :
    Irrational (∑' n : ℕ, 1 / (((n + 2).factorial : ℝ) - 1)) := by
  apply irrational_of_arbitrarily_large_escapes
  intro M
  obtain ⟨N, hMN, hN⟩ := hescape M
  refine ⟨N, hMN, ?_⟩
  simpa only [Corridor, scaledPrefix, prefix_eq_sum_Icc, factorialTerm] using hN

lemma factorial_mul_term (n : ℕ) (hn : 2 ≤ n) :
    (n.factorial : ℝ) * factorialTerm n = 1 + factorialTerm n := by
  have hd : (n.factorial : ℝ) - 1 ≠ 0 := by
    linarith [factorial_ge_two n hn]
  unfold factorialTerm
  field_simp
  ring

lemma scaled_prefix_succ (N : ℕ) (hN : 1 ≤ N) :
    scaledPrefix (N + 1) = ((N : ℝ) + 1) * scaledPrefix N +
      1 + factorialTerm (N + 1) := by
  unfold scaledPrefix
  rw [prefix_succ, mul_add, factorial_mul_term (N + 1) (by omega),
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  ring

lemma factorialTerm_lt_half (n : ℕ) (hn : 3 ≤ n) :
    factorialTerm n < 1 / 2 := by
  have hfac : (6 : ℝ) ≤ n.factorial := by
    exact_mod_cast (show 6 ≤ n.factorial from
      (by simpa using Nat.factorial_le hn))
  unfold factorialTerm
  exact one_div_lt_one_div_of_lt (by norm_num) (by linarith)

/-- Consecutive corridor membership forces an exact integral carry. -/
theorem carry_recurrence_of_corridor (N : ℕ) (hN : 3 ≤ N)
    (hC : Corridor N) (hC' : Corridor (N + 1)) :
    carry (N + 1) = ((N : ℤ) + 1) * carry N := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  change 1 - 1 / (N : ℝ) < Int.fract (scaledPrefix N) ∧
    Int.fract (scaledPrefix N) < 1 - 1 / ((N : ℝ) + 1) at hC
  have hCnext : 1 - 1 / ((N : ℝ) + 1) < Int.fract (scaledPrefix (N + 1)) := by
    simpa only [Corridor, Set.mem_Ioo, Nat.cast_add, Nat.cast_one] using hC'.1
  have hg0 : 0 < 1 - Int.fract (scaledPrefix (N + 1)) :=
    sub_pos.mpr (Int.fract_lt_one _)
  have hg1 : 1 - Int.fract (scaledPrefix (N + 1)) < 1 / 2 := by
    have hr : 1 / ((N : ℝ) + 1) < (1 : ℝ) / 2 :=
      one_div_lt_one_div_of_lt (by norm_num) (by linarith)
    linarith
  have hr : 1 / (N : ℝ) < 1 :=
    (div_lt_one (by linarith)).2 (by linarith)
  have hmul : ((N : ℝ) + 1) * (1 / (N : ℝ)) = 1 + 1 / (N : ℝ) := by
    field_simp
  have hglarge : ((N : ℝ) + 1) * (1 - Int.fract (scaledPrefix N)) < 2 := by
    have h := mul_lt_mul_of_pos_left
      (show 1 - Int.fract (scaledPrefix N) < 1 / (N : ℝ) by linarith [hC.1])
      (show (0 : ℝ) < (N : ℝ) + 1 by linarith)
    rw [hmul] at h
    linarith
  have hgsmall : 1 < ((N : ℝ) + 1) * (1 - Int.fract (scaledPrefix N)) := by
    have h := mul_lt_mul_of_pos_left
      (show 1 / ((N : ℝ) + 1) < 1 - Int.fract (scaledPrefix N) by linarith [hC.2])
      (show (0 : ℝ) < (N : ℝ) + 1 by linarith)
    have heq : ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1)) = 1 := by field_simp
    rwa [heq] at h
  let d : ℤ := carry (N + 1) - ((N : ℤ) + 1) * carry N
  have hd : (d : ℝ) = 1 + factorialTerm (N + 1) +
      (1 - Int.fract (scaledPrefix (N + 1))) -
      ((N : ℝ) + 1) * (1 - Int.fract (scaledPrefix N)) := by
    dsimp only [d]
    push_cast
    rw [carry_cast, carry_cast, scaled_prefix_succ N (by omega)]
    ring
  have hterm0 := factorialTerm_pos (N + 1) (by omega)
  have hterm1 := factorialTerm_lt_half (N + 1) (by omega)
  have hdl : (-1 : ℝ) < (d : ℝ) := by rw [hd]; linarith
  have hdu : (d : ℝ) < 1 := by rw [hd]; linarith
  have hdl' : (-1 : ℤ) < d := by exact_mod_cast hdl
  have hdu' : d < (1 : ℤ) := by exact_mod_cast hdu
  have hd0 : d = 0 := by omega
  exact sub_eq_zero.mp hd0

noncomputable def normalizedCarry (N : ℕ) : ℝ :=
  (carry N : ℝ) / (N.factorial : ℝ)

lemma finitePrefix_tendsto : Tendsto finitePrefix atTop (𝓝 S) := by
  have hs : HasSum factorialTerm S := by
    simpa only [S_eq_tsum_factorialTerm] using summable_factorialTerm.hasSum
  exact (tendsto_add_atTop_iff_nat 1).2 hs.tendsto_sum_nat

lemma inverse_factorial_tendsto_zero :
    Tendsto (fun N : ℕ => 1 / (N.factorial : ℝ)) atTop (𝓝 0) := by
  simpa only [one_pow] using FloorSemiring.tendsto_pow_div_factorial_atTop (1 : ℝ)

/-- Normalizing the integral carry always converges to the series sum. -/
lemma normalizedCarry_tendsto : Tendsto normalizedCarry atTop (𝓝 S) := by
  let error : ℕ → ℝ := fun N =>
    (1 - Int.fract (scaledPrefix N)) / (N.factorial : ℝ)
  have herror : Tendsto error atTop (𝓝 0) := by
    apply squeeze_zero _ _ inverse_factorial_tendsto_zero
    · intro N
      exact div_nonneg (sub_nonneg.mpr (Int.fract_lt_one _).le)
        (Nat.cast_nonneg _)
    · intro N
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      linarith [Int.fract_nonneg (scaledPrefix N)]
  have heq (N : ℕ) : finitePrefix N + error N = normalizedCarry N := by
    have hF : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
    dsimp only [error, normalizedCarry]
    rw [carry_cast]
    unfold scaledPrefix
    field_simp
    ring
  simpa only [add_zero] using (finitePrefix_tendsto.add herror).congr heq

lemma normalizedCarry_step (N : ℕ)
    (hrec : carry (N + 1) = ((N : ℤ) + 1) * carry N) :
    normalizedCarry (N + 1) = normalizedCarry N := by
  unfold normalizedCarry
  rw [hrec, Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hF : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  field_simp

/-- An eventually exact integral carry recurrence is sufficient for
rationality; no escape or corridor assumption is needed for this direction. -/
theorem rational_of_eventually_carry
    (hrec : ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      carry (N + 1) = ((N : ℤ) + 1) * carry N) :
    ∃ q : ℚ, S = (q : ℝ) := by
  obtain ⟨M, hrec⟩ := hrec
  have hconstant : ∀ N : ℕ, M ≤ N → normalizedCarry N = normalizedCarry M := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => rfl
    | succ N hN ih =>
      rw [normalizedCarry_step N (hrec N hN), ih]
  have ht : Tendsto normalizedCarry atTop (𝓝 (normalizedCarry M)) :=
    Filter.Tendsto.congr'
      (eventually_atTop.mpr ⟨M, fun N hN => (hconstant N hN).symm⟩)
      tendsto_const_nhds
  have heq : S = normalizedCarry M := tendsto_nhds_unique normalizedCarry_tendsto ht
  refine ⟨(carry M : ℚ) / (M.factorial : ℚ), ?_⟩
  simpa only [normalizedCarry, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using heq

/-- Rationality is equivalent to eventual membership in the open corridor. -/
theorem rational_iff_eventually_corridor :
    (∃ q : ℚ, S = (q : ℝ)) ↔ ∃ M : ℕ, ∀ N : ℕ, M ≤ N → Corridor N := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨max q.den 3, fun N hN => ?_⟩
    exact rational_implies_corridor q hq N
      ((le_max_right q.den 3).trans hN) ((le_max_left q.den 3).trans hN)
  · rintro ⟨M, hC⟩
    apply rational_of_eventually_carry
    refine ⟨max M 3, fun N hN => ?_⟩
    exact carry_recurrence_of_corridor N ((le_max_right M 3).trans hN)
      (hC N ((le_max_left M 3).trans hN)) (hC (N + 1) (by omega))

/-- Rationality is also equivalent to an eventually exact integer carry
recurrence for the factorial-scaled finite prefixes. -/
theorem rational_iff_eventually_carry :
    (∃ q : ℚ, S = (q : ℝ)) ↔ ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      carry (N + 1) = ((N : ℤ) + 1) * carry N := by
  constructor
  · intro hq
    obtain ⟨M, hC⟩ := rational_iff_eventually_corridor.mp hq
    refine ⟨max M 3, fun N hN => ?_⟩
    exact carry_recurrence_of_corridor N ((le_max_right M 3).trans hN)
      (hC N ((le_max_left M 3).trans hN)) (hC (N + 1) (by omega))
  · exact rational_of_eventually_carry

/-- Exact escape characterization.  This does not supply either side of the
 equivalence unconditionally. -/
theorem irrational_iff_arbitrarily_large_escapes :
    Irrational S ↔ ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ ¬ Corridor N := by
  constructor
  · intro hI M
    by_contra h
    have hC : ∀ N : ℕ, M ≤ N → Corridor N := by
      intro N hMN
      by_contra hnot
      exact h ⟨N, hMN, hnot⟩
    obtain ⟨q, hq⟩ := rational_iff_eventually_corridor.mpr ⟨M, hC⟩
    exact hI ⟨q, hq.symm⟩
  · exact irrational_of_arbitrarily_large_escapes

set_option maxHeartbeats 0 in
set_option maxRecDepth 4096 in
/-- An exact finite escape certificate. This is not a proof of infinitely many escapes. -/
theorem not_corridor_two_hundred : ¬ Corridor 200 := by
  norm_num [Corridor, scaledPrefix, finitePrefix, factorialTerm,
    Finset.sum_range_succ, Nat.factorial, Int.fract]

/-- A hypothetical rational value cannot have denominator dividing `200!`. -/
theorem denominator_not_dvd_two_hundred_factorial (q : ℚ) (hq : S = (q : ℝ)) :
    ¬ q.den ∣ Nat.factorial 200 := by
  intro hdiv
  apply not_corridor_two_hundred
  apply corridor_of_integral_scaled_sum 200 (by norm_num)
  simpa only [hq] using factorial_mul_rat_integral_of_dvd q 200 hdiv

/-- In particular, every hypothetical rational representation has denominator above 200. -/
theorem denominator_gt_two_hundred (q : ℚ) (hq : S = (q : ℝ)) :
    200 < q.den := by
  by_contra h
  exact denominator_not_dvd_two_hundred_factorial q hq
    (Nat.dvd_factorial q.den_pos (by omega))

end FactorialCarryCriterion
