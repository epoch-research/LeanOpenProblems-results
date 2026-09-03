import FormalConjecturesUtil

/-!
# The non-strict modified Engel rule also need not terminate on rationals

This is an auxiliary observation, not a proof or disproof of Erdos 68.
Starting with A=2 and r=1/4, every available denominator A*q-1 is odd.
The remainder's reduced denominator remains even, so it cannot become zero.
-/

namespace CeilingEngelDevelopment

def digit (A : ℕ) (r : ℚ) : ℕ := ⌈(1 / r + 1) / (A : ℚ)⌉₊

def step (s : ℕ × ℚ) : ℕ × ℚ :=
  let B := s.1 * digit s.1 s.2
  (B, s.2 - 1 / ((B - 1 : ℕ) : ℚ))

private lemma coprime_den_add {x y : ℚ}
    (hx : Nat.Coprime 2 x.den) (hy : Nat.Coprime 2 y.den) :
    Nat.Coprime 2 (x + y).den :=
  (hx.mul_right hy).of_dvd_right (Rat.add_den_dvd x y)

lemma reciprocal_odd_den {d : ℕ} (hd : 0 < d) (ho : d % 2 = 1) :
    Nat.Coprime 2 (1 / (d : ℚ)).den := by
  rw [one_div, Rat.inv_natCast_den_of_pos hd, Nat.coprime_two_left]
  exact Nat.odd_iff.mpr ho

lemma step_denominator_pos {A : ℕ} {r : ℚ} (hA : 0 < A) (hr : 0 < r) :
    1 < A * digit A r ∧ 1 / r ≤ ((A * digit A r - 1 : ℕ) : ℚ) := by
  have hAp : (0 : ℚ) < A := by exact_mod_cast hA
  have hc := Nat.le_ceil ((1 / r + 1) / (A : ℚ))
  change (1 / r + 1) / (A : ℚ) ≤ (digit A r : ℚ) at hc
  have h : 1 / r + 1 ≤ (A * digit A r : ℕ) := by
    rw [div_le_iff₀ hAp] at hc
    push_cast
    nlinarith
  have hB : 1 < A * digit A r := by
    have hp : (0 : ℚ) < 1 / r := one_div_pos.mpr hr
    have hh : (1 : ℚ) < (A * digit A r : ℕ) := by linarith
    exact_mod_cast hh
  refine ⟨hB, ?_⟩
  rw [Nat.cast_sub (by omega : 1 ≤ A * digit A r), Nat.cast_one]
  linarith

lemma step_preserves_invariant {A : ℕ} {r : ℚ}
    (hA : 0 < A) (hAe : Even A) (hr : 0 < r)
    (hden : ¬Nat.Coprime 2 r.den) :
    0 < (step (A, r)).1 ∧ Even (step (A, r)).1 ∧
      0 < (step (A, r)).2 ∧ ¬Nat.Coprime 2 (step (A, r)).2.den := by
  obtain ⟨hB, hbound⟩ := step_denominator_pos hA hr
  have he : Even (A * digit A r) := hAe.mul_right _
  have hm : (A * digit A r) % 2 = 0 := Nat.even_iff.mp he
  have ho : (A * digit A r - 1) % 2 = 1 := by omega
  have hd : 0 < A * digit A r - 1 := by omega
  have hc := reciprocal_odd_den hd ho
  have hn : ¬Nat.Coprime 2
      (r - 1 / ((A * digit A r - 1 : ℕ) : ℚ)).den := by
    intro hh
    have hh' := coprime_den_add hh hc
    simp only [sub_add_cancel] at hh'
    exact hden hh'
  have hnn : 0 ≤ r - 1 / ((A * digit A r - 1 : ℕ) : ℚ) := by
    have hh := one_div_le_one_div_of_le (one_div_pos.mpr hr) hbound
    rw [one_div_one_div] at hh
    linarith
  have hne : r - 1 / ((A * digit A r - 1 : ℕ) : ℚ) ≠ 0 := by
    intro hh
    rw [hh] at hn
    norm_num at hn
  exact ⟨by simpa [step] using (show 0 < A * digit A r by omega),
    by simpa [step] using he,
    by simpa [step] using lt_of_le_of_ne hnn (Ne.symm hne),
    by simpa [step] using hn⟩

lemma iterate_invariant (n : ℕ) :
    0 < ((step^[n]) (2, (1 / 4 : ℚ))).1 ∧
      Even ((step^[n]) (2, (1 / 4 : ℚ))).1 ∧
      0 < ((step^[n]) (2, (1 / 4 : ℚ))).2 ∧
      ¬Nat.Coprime 2 ((step^[n]) (2, (1 / 4 : ℚ))).2.den := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact step_preserves_invariant ih.1 ih.2.1 ih.2.2.1 ih.2.2.2

/-- Even without a strict floor-plus-one convention, this modified rule has
positive rational inputs whose remainders never become zero. -/
theorem rational_input_never_terminates (n : ℕ) :
    0 < ((step^[n]) (2, (1 / 4 : ℚ))).2 :=
  (iterate_invariant n).2.2.1

lemma first_step : step (2, (1 / 4 : ℚ)) = (6, (1 / 20 : ℚ)) := by
  norm_num [step, digit]

lemma step_contraction {A : ℕ} {r : ℚ} (hA : 0 < A) (hr : 0 < r)
    (hsize : ((A : ℚ) + 1) * r ≤ 3 / 4) :
    (step (A, r)).2 ≤ r / 2 ∧
      (((step (A, r)).1 : ℚ) + 1) * (step (A, r)).2 ≤ 3 / 4 := by
  obtain ⟨hB, _⟩ := step_denominator_pos hA hr
  let B := A * digit A r
  let d : ℚ := ((B - 1 : ℕ) : ℚ)
  have hd : 0 < d := by
    dsimp [d, B]
    exact_mod_cast (show 0 < A * digit A r - 1 by omega)
  have heq : (B : ℚ) = d + 1 := by
    dsimp [d]
    rw [Nat.cast_sub (by dsimp [B]; omega), Nat.cast_one]
    ring
  have hAp : (0 : ℚ) < A := by exact_mod_cast hA
  have hu := Nat.ceil_lt_add_one (show (0 : ℚ) ≤ (1 / r + 1) / A by positivity)
  change (digit A r : ℚ) < (1 / r + 1) / A + 1 at hu
  have hu' := mul_lt_mul_of_pos_right hu hAp
  have hU : d < 1 / r + A := by
    dsimp [B] at heq
    push_cast at heq
    rw [add_mul, div_mul_cancel₀ _ hAp.ne', one_mul] at hu'
    nlinarith
  have hp := mul_lt_mul_of_pos_right hU hr
  have hdr : d * r < 1 + (A : ℚ) * r := by
    rwa [add_mul, one_div_mul_cancel hr.ne'] at hp
  have hAr : (A : ℚ) * r < 1 := by nlinarith
  have hc : r - 1 / d ≤ r / 2 := by
    have hh : r / 2 ≤ 1 / d := (le_div_iff₀ hd).mpr (by nlinarith)
    linarith
  have hid : d * (r - 1 / d) = d * r - 1 := by
    rw [mul_sub, mul_one_div_cancel hd.ne']
  have hs : ((B : ℚ) + 1) * (r - 1 / d) ≤ 3 / 4 := by
    rw [heq]
    nlinarith
  exact ⟨by simpa [step, B, d] using hc, by simpa [step, B, d] using hs⟩

def state (n : ℕ) : ℕ × ℚ := (step^[n]) (2, (1 / 4 : ℚ))

lemma state_zero : state 0 = (2, (1 / 4 : ℚ)) := rfl

lemma state_succ (n : ℕ) : state (n + 1) = step (state n) :=
  Function.iterate_succ_apply' _ _ _

lemma state_size (n : ℕ) : (((state n).1 : ℚ) + 1) * (state n).2 ≤ 3 / 4 := by
  induction n with
  | zero => norm_num [state]
  | succ n ih =>
    rw [state_succ]
    exact (step_contraction (iterate_invariant n).1 (iterate_invariant n).2.2.1 ih).2

lemma state_remainder_le (n : ℕ) : (state n).2 ≤ (1 / 4 : ℚ) * (1 / 2) ^ n := by
  induction n with
  | zero => norm_num [state]
  | succ n ih =>
    have h := (step_contraction (iterate_invariant n).1
      (iterate_invariant n).2.2.1 (state_size n)).1
    rw [state_succ]
    calc
      (step (state n)).2 ≤ (state n).2 / 2 := h
      _ ≤ ((1 / 4 : ℚ) * (1 / 2) ^ n) / 2 := by gcongr
      _ = (1 / 4 : ℚ) * (1 / 2) ^ (n + 1) := by ring

def denominator (n : ℕ) : ℕ := (state (n + 1)).1 - 1

lemma first_denominators : denominator 0 = 5 ∧ denominator 1 = 23 ∧ denominator 2 = 167 := by
  norm_num [denominator, state, Function.iterate_succ_apply', step, digit]


lemma denominator_pos (n : ℕ) : 0 < denominator n := by
  have h := (step_denominator_pos (iterate_invariant n).1
    (iterate_invariant n).2.2.1).1
  simp only [denominator, state_succ, step]
  change 0 < (state n).1 * digit (state n).1 (state n).2 - 1
  change 1 < (state n).1 * digit (state n).1 (state n).2 at h
  omega

lemma denominator_odd (n : ℕ) : Odd (denominator n) := by
  have he := (iterate_invariant (n + 1)).2.1
  change Even (state (n + 1)).1 at he
  have hm := Nat.even_iff.mp he
  have hp := denominator_pos n
  apply Nat.odd_iff.mpr
  dsimp [denominator] at hp ⊢
  omega

lemma denominator_succ_chain (n : ℕ) : denominator n + 1 ∣ denominator (n + 1) + 1 := by
  have h1 := denominator_pos n
  have h2 := denominator_pos (n + 1)
  have he (k : ℕ) (hk : 0 < denominator k) :
      denominator k + 1 = (state (k + 1)).1 := by
    dsimp [denominator] at hk ⊢
    omega
  rw [he n h1, he (n + 1) h2, state_succ (n + 1)]
  exact dvd_mul_right _ _

lemma remainder_difference (n : ℕ) :
    (state n).2 - (state (n + 1)).2 = 1 / (denominator n : ℚ) := by
  simp only [denominator, state_succ, step]
  ring

open Filter
open scoped Topology

lemma remainder_tendsto_zero :
    Tendsto (fun n => ((state n).2 : ℝ)) atTop (𝓝 0) := by
  have hg : Tendsto (fun n : ℕ => (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (1 / 4 : ℝ)
  apply squeeze_zero _ _ hg
  · intro n
    exact_mod_cast (rational_input_never_terminates n).le
  · intro n
    have hh := (Rat.cast_le (K := ℝ)).2 (state_remainder_le n)
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hh

lemma hasSum_denominator_reciprocals :
    HasSum (fun n : ℕ => 1 / (denominator n : ℝ)) (1 / 4 : ℝ) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity) _).mpr
  have he (n : ℕ) :
      (∑ k ∈ Finset.range n, 1 / (denominator k : ℝ)) =
        (1 / 4 : ℝ) - ((state n).2 : ℝ) := by
    have hd (k : ℕ) : (1 / (denominator k : ℝ)) =
        ((state k).2 : ℝ) - ((state (k + 1)).2 : ℝ) := by
      have hh := congrArg (fun x : ℚ => (x : ℝ)) (remainder_difference k).symm
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Rat.cast_sub] using hh
    simp_rw [hd]
    rw [Finset.sum_range_sub']
    norm_num [state]
  simp_rw [he]
  simpa using tendsto_const_nhds.sub remainder_tendsto_zero

/-- A rational reciprocal series with odd denominators and a divisibility
chain after adding one. Its denominators are not the original factorials
minus one. -/
theorem rational_chain_series :
    (∀ n, 0 < denominator n ∧ Odd (denominator n)) ∧
      (∀ n, denominator n + 1 ∣ denominator (n + 1) + 1) ∧
      (∑' n : ℕ, 1 / (denominator n : ℝ)) = (1 / 4 : ℝ) :=
  ⟨fun n => ⟨denominator_pos n, denominator_odd n⟩,
    denominator_succ_chain, hasSum_denominator_reciprocals.tsum_eq⟩

#print axioms rational_input_never_terminates
#print axioms rational_chain_series

end CeilingEngelDevelopment
