import Submission.PrimeCountingLower

/-! Prime-counting discrepancies on a four-adic sequence exceed every constant
multiple of the square root, using only elementary Chebyshev estimates. -/
namespace Erdos970.PrimeCountingDyadic
open Filter Real

lemma density_tendsto_zero :
    Tendsto (fun n : ℕ => (n.primeCounting : ℝ) / n) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hcheb : ∀ᶠ n : ℕ in atTop,
      (n.primeCounting : ℝ) ≤ (log 4 + 1) * n / log n := by
    simpa only [Nat.floor_natCast] using ht.eventually
      (Chebyshev.eventually_primeCounting_le (ε := 1) (by norm_num))
  have hbound : ∀ᶠ n : ℕ in atTop,
      (n.primeCounting : ℝ) / n ≤ (log 4 + 1) / log n := by
    filter_upwards [hcheb, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply (div_le_iff₀ hn0).mpr
    convert hn using 1; ring
  exact squeeze_zero' (Eventually.of_forall (fun n => by positivity)) hbound
    ((tendsto_log_atTop.comp ht).const_div_atTop (log 4 + 1))

lemma nat_sq_le_two_pow (n : ℕ) (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction t with
  | zero => norm_num
  | succ t ih =>
    have hi := ih (by omega)
    calc
      (4 + (t + 1)) ^ 2 ≤ 2 * (4 + t) ^ 2 := by nlinarith
      _ ≤ 2 * 2 ^ (4 + t) := Nat.mul_le_mul_left 2 hi
      _ = 2 ^ (4 + (t + 1)) := by rw [show 4 + (t + 1) = (4 + t) + 1 by omega, pow_succ]; ring

lemma exists_four_power_count_gt (D N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ (D : ℝ) * 2 ^ n < (4 ^ n).primeCounting := by
  let n := 8 * D + N + 4
  have hn4 : 4 ≤ n := by dsimp [n]; omega
  have hnpos : 0 < n := by omega
  have hnD : (8 * D : ℝ) < n := by exact_mod_cast (show 8 * D < n by dsimp [n]; omega)
  refine ⟨n, by dsimp [n]; omega, ?_⟩
  have hx : 2 ≤ 4 ^ n := by
    have hh := Nat.le_self_pow hnpos.ne' 4
    omega
  have hl := PrimeCountingLower.log_bound (4 ^ n) hx
  have hl4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, log_pow]; norm_num
  simp only [Nat.cast_pow, Nat.cast_ofNat, log_pow, hl4] at hl
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hmain : (4 : ℝ) ^ n ≤ 8 * n * (4 ^ n).primeCounting := by nlinarith
  have hpow : (4 : ℝ) ^ n = (2 ^ n) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul, Nat.mul_comm, pow_mul]
  have hn2 : (n : ℝ) ^ 2 ≤ 2 ^ n := by exact_mod_cast nat_sq_le_two_pow n hn4
  have hnp : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  by_contra h
  have hle : ((4 ^ n).primeCounting : ℝ) ≤ D * 2 ^ n := le_of_not_gt h
  have hmul := mul_le_mul_of_nonneg_left hle (by positivity : (0 : ℝ) ≤ 8 * n)
  rw [hpow] at hmain
  have hroot : (2 : ℝ) ^ n ≤ 8 * n * D := by nlinarith
  nlinarith

/-- A square-root error in a four-adic scaling recurrence, together with zero
limiting density, forces a square-root bound for the counting function itself. -/
lemma bound_of_recurrence (f : ℕ → ℝ) (B : ℝ)
    (hlim : Tendsto (fun n => f n / 4 ^ n) atTop (nhds 0))
    (hstep : ∀ n, 4 * f n - f (n + 1) ≤ B * 2 ^ n) :
    ∀ n, f n ≤ (B / 2) * 2 ^ n := by
  let g := fun n : ℕ => (f n - (B / 2) * 2 ^ n) / 4 ^ n
  have hgeq (n : ℕ) : g n = f n / 4 ^ n - (B / 2) * (1 / 2 : ℝ) ^ n := by
    dsimp only [g]
    rw [sub_div, mul_div_assoc, ← div_pow]
    norm_num
  have hmono : Monotone g := by
    apply monotone_nat_of_le_succ
    intro n
    have hg0 : (0 : ℝ) < 4 ^ n := by positivity
    have hnum : 0 ≤ f (n + 1) - 4 * f n + B * 2 ^ n := by linarith [hstep n]
    have hid : g (n + 1) - g n =
        (f (n + 1) - 4 * f n + B * 2 ^ n) / (4 ^ n * 4) := by
      dsimp only [g]
      rw [pow_succ, pow_succ]
      field_simp [hg0.ne']
      <;> ring
    have hnonneg : 0 ≤ g (n + 1) - g n := by rw [hid]; positivity
    linarith
  have hglim : Tendsto g atTop (nhds 0) := by
    rw [show g = (fun n => f n / 4 ^ n - (B / 2) * (1 / 2 : ℝ) ^ n) from funext hgeq]
    convert hlim.sub (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))) using 1
    ring
  intro n
  have hg : g n ≤ 0 := ge_of_tendsto hglim
    (by filter_upwards [eventually_ge_atTop n] with m hm; exact hmono hm)
  have hg' : f n - (B / 2) * 2 ^ n ≤ 0 := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ n)).mp hg
    simpa only [zero_mul] using h
  linarith

/-- No uniform square-root bound holds for these prime-counting differences. -/
theorem not_bounded_four_adic_difference :
    ¬∃ B : ℝ, ∀ n : ℕ,
      |((4 ^ (n + 1)).primeCounting : ℝ) - 4 * (4 ^ n).primeCounting| ≤ B * 2 ^ n := by
  rintro ⟨B, hB⟩
  have hlim : Tendsto (fun n : ℕ => ((4 ^ n).primeCounting : ℝ) / (4 : ℝ) ^ n) atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_pow, Nat.cast_ofNat] using
      density_tendsto_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 4))
  have hb := bound_of_recurrence (fun n => ((4 ^ n).primeCounting : ℝ)) B hlim
    (fun n => by have h := (abs_le.mp (hB n)).1; linarith)
  obtain ⟨D, hD⟩ := exists_nat_gt (B / 2)
  obtain ⟨n, hn, hlarge⟩ := exists_four_power_count_gt D 0
  have hmul := mul_le_mul_of_nonneg_right hD.le (by positivity : (0 : ℝ) ≤ 2 ^ n)
  have hsmall := hb n
  linarith

/-- Discarding finitely many four-adic arguments does not repair the bound. -/
theorem not_eventually_bounded_four_adic_difference (B : ℝ) :
    ¬∀ᶠ n : ℕ in atTop,
      |((4 ^ (n + 1)).primeCounting : ℝ) - 4 * (4 ^ n).primeCounting| ≤ B * 2 ^ n := by
  intro hevent
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let f := fun n : ℕ => |((4 ^ (n + 1)).primeCounting : ℝ) - 4 * (4 ^ n).primeCounting|
  let H := ∑ n ∈ Finset.range N, f n / 2 ^ n
  apply not_bounded_four_adic_difference
  refine ⟨max B H, fun n => ?_⟩
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp.le)
  · have hterm : f n / 2 ^ n ≤ H := Finset.single_le_sum
      (s := Finset.range N) (f := fun j => f j / 2 ^ j)
      (fun j _ => div_nonneg (abs_nonneg _) (by positivity)) (Finset.mem_range.mpr (by omega))
    have hbound : f n ≤ H * 2 ^ n := (div_le_iff₀ hp).mp hterm
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp.le)

#print axioms not_eventually_bounded_four_adic_difference
#print axioms density_tendsto_zero
#print axioms not_bounded_four_adic_difference
end Erdos970.PrimeCountingDyadic
