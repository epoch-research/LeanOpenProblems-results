import FormalConjecturesUtil

/-!
An unconditional prime-power error bound for the von Mangoldt correlation in
Erdős 972. This does not establish a lower bound for that correlation.
-/
namespace Erdos972PrimePowerError

open Finset ArithmeticFunction

noncomputable def floorMul (α : ℝ) (n : ℕ) : ℕ := ⌊α * n⌋₊

lemma self_le_floorMul {α : ℝ} (hα : 1 ≤ α) (n : ℕ) : n ≤ floorMul α n := by
  apply Nat.le_floor
  exact le_mul_of_one_le_left (Nat.cast_nonneg n) hα

lemma floorMul_strictMono {α : ℝ} (hα : 1 ≤ α) : StrictMono (floorMul α) := by
  intro m n hmn
  apply Nat.lt_of_succ_le
  apply Nat.le_floor
  have hm : (floorMul α m : ℝ) ≤ α * m := Nat.floor_le (by positivity)
  have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hmn
  push_cast
  nlinarith

lemma floorMul_pos {α : ℝ} (hα : 1 ≤ α) {n : ℕ} (hn : 0 < n) :
    0 < floorMul α n := hn.trans_le (self_le_floorMul hα n)

lemma floorMul_le_real {α : ℝ} (hα : 1 ≤ α) {n N : ℕ} (hn : n ≤ N) :
    (floorMul α n : ℝ) ≤ α * N := by
  exact (Nat.floor_le (by positivity)).trans
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hn) (by linarith))

lemma log_floorMul_le {α : ℝ} (hα : 1 ≤ α) {n N : ℕ}
    (hn : n ∈ Ioc 0 N) : Real.log (floorMul α n) ≤ Real.log (α * N) := by
  exact Real.log_le_log (Nat.cast_pos.mpr (floorMul_pos hα (mem_Ioc.mp hn).1))
    (floorMul_le_real hα (mem_Ioc.mp hn).2)

lemma log_input_le {n N : ℕ} (hn : n ∈ Ioc 0 N) :
    Real.log n ≤ Real.log N := by
  exact Real.log_le_log (Nat.cast_pos.mpr (mem_Ioc.mp hn).1)
    (Nat.cast_le.mpr (mem_Ioc.mp hn).2)

lemma sum_nonprime_outputs_le {α : ℝ} (hα : 1 ≤ α) (N : ℕ) :
    (∑ n ∈ (Ioc 0 N).filter (fun n => ¬ (floorMul α n).Prime), Λ (floorMul α n)) ≤
      Chebyshev.psi (α * N) - Chebyshev.theta (α * N) := by
  classical
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
  let s := (Ioc 0 N).filter (fun n => ¬ (floorMul α n).Prime)
  calc
    _ = ∑ q ∈ s.image (floorMul α), Λ q := by
      rw [sum_image]
      exact fun _ _ _ _ h => (floorMul_strictMono hα).injective h
    _ ≤ ∑ q ∈ (Ioc 0 ⌊α * N⌋₊).filter (fun q => ¬ q.Prime), Λ q := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro q hq
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hq
        obtain ⟨hn, hnp⟩ := mem_filter.mp hn
        refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨floorMul_pos hα (mem_Ioc.mp hn).1, ?_⟩, hnp⟩
        exact (floorMul_strictMono hα).monotone (mem_Ioc.mp hn).2
      · intro q _ _
        exact vonMangoldt_nonneg

noncomputable def mangoldtCorrelation (α : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, Λ n * Λ (floorMul α n)

noncomputable def primeCorrelation (α : ℝ) (N : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ (Ioc 0 N).filter (fun n => n.Prime ∧ (floorMul α n).Prime),
    Real.log n * Real.log (floorMul α n)

lemma primeCorrelation_le (α : ℝ) (N : ℕ) :
    primeCorrelation α N ≤ mangoldtCorrelation α N := by
  classical
  unfold primeCorrelation mangoldtCorrelation
  rw [sum_filter]
  apply sum_le_sum
  intro n _
  split_ifs with h
  · rw [vonMangoldt_apply_prime h.1, vonMangoldt_apply_prime h.2]
  · exact mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg

/-- Only non-prime prime powers can contribute to this difference. -/
lemma correlation_sub_le_psi_sub_theta {α : ℝ} (hα : 1 ≤ α) {N : ℕ} (hN : 1 ≤ N) :
    mangoldtCorrelation α N - primeCorrelation α N ≤
      Real.log (α * N) * (Chebyshev.psi N - Chebyshev.theta N) +
      Real.log N * (Chebyshev.psi (α * N) - Chebyshev.theta (α * N)) := by
  classical
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlogY : 0 ≤ Real.log (α * N) := Real.log_nonneg (by
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith)
  have hpoint (n : ℕ) (hn : n ∈ Ioc 0 N) :
      Λ n * Λ (floorMul α n) ≤
        (if n.Prime ∧ (floorMul α n).Prime then Real.log n * Real.log (floorMul α n) else 0) +
        (if ¬n.Prime then Real.log (α * N) * Λ n else 0) +
        (if ¬(floorMul α n).Prime then Real.log N * Λ (floorMul α n) else 0) := by
    have hi : Λ n ≤ Real.log N := vonMangoldt_le_log.trans (log_input_le hn)
    have ho : Λ (floorMul α n) ≤ Real.log (α * N) :=
      vonMangoldt_le_log.trans (log_floorMul_le hα hn)
    by_cases hp : n.Prime
    · by_cases hq : (floorMul α n).Prime
      · simp [hp, hq, vonMangoldt_apply_prime hp, vonMangoldt_apply_prime hq]
      · simp only [hp, hq, and_false, not_true_eq_false, not_false_eq_true, if_true, if_false,
          zero_add, add_zero]
        exact mul_le_mul_of_nonneg_right hi vonMangoldt_nonneg
    · simp only [hp, false_and, not_false_eq_true, if_true, if_false, zero_add]
      have hmain : Λ n * Λ (floorMul α n) ≤ Real.log (α * N) * Λ n := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left ho (vonMangoldt_nonneg (n := n))
      apply hmain.trans
      apply le_add_of_nonneg_right
      split_ifs <;> first | exact mul_nonneg hlogN vonMangoldt_nonneg | exact le_rfl
  have hs := sum_le_sum hpoint
  simp only [sum_add_distrib] at hs
  have hi : (∑ n ∈ Ioc 0 N, if ¬n.Prime then Real.log (α * N) * Λ n else 0) =
      Real.log (α * N) * (Chebyshev.psi N - Chebyshev.theta N) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, mul_sum, sum_filter]
  have ho : (∑ n ∈ Ioc 0 N, if ¬(floorMul α n).Prime then
      Real.log N * Λ (floorMul α n) else 0) ≤
      Real.log N * (Chebyshev.psi (α * N) - Chebyshev.theta (α * N)) := by
    rw [← sum_filter, ← mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_nonprime_outputs_le hα N) hlogN
  have hp : (∑ n ∈ Ioc 0 N, if n.Prime ∧ (floorMul α n).Prime then
      Real.log n * Real.log (floorMul α n) else 0) = primeCorrelation α N := by
    rw [primeCorrelation, sum_filter]
  change mangoldtCorrelation α N ≤ _ at hs
  rw [hi, hp] at hs
  linarith

/-- An explicit `O_α(√N log² N)` bound for the contribution that does not come from
pairs of primes. It supplies an error bound, not a lower bound for the correlation. -/
theorem prime_power_error_bound {α : ℝ} (hα : 1 ≤ α) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ mangoldtCorrelation α N - primeCorrelation α N ∧
    mangoldtCorrelation α N - primeCorrelation α N ≤
      2 * Real.log N * Real.log (α * N) * (Real.sqrt N + Real.sqrt (α * N)) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hY : (1 : ℝ) ≤ α * N := by nlinarith
  have hlogN := Real.log_nonneg hN'
  have hlogY := Real.log_nonneg hY
  refine ⟨sub_nonneg.mpr (primeCorrelation_le α N), ?_⟩
  apply (correlation_sub_le_psi_sub_theta hα hN).trans
  have hi := (le_abs_self (Chebyshev.psi N - Chebyshev.theta N)).trans
    (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hN')
  have ho := (le_abs_self (Chebyshev.psi (α * N) - Chebyshev.theta (α * N))).trans
    (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hY)
  calc
    _ ≤ Real.log (α * N) * (2 * Real.sqrt N * Real.log N) +
        Real.log N * (2 * Real.sqrt (α * N) * Real.log (α * N)) :=
      add_le_add (mul_le_mul_of_nonneg_left hi hlogY) (mul_le_mul_of_nonneg_left ho hlogN)
    _ = _ := by ring

#print axioms prime_power_error_bound

/-- Separating squares from higher prime powers removes the logarithm in the
standard elementary `ψ - θ` bound. -/
theorem psi_sub_theta_le_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (Real.log 4 + 12) * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  by_cases hx2 : x < 2
  · rw [Chebyshev.psi_eq_zero_of_lt_two hx2,
      Chebyshev.theta_eq_zero_of_lt_two hx2, sub_self]
    positivity
  have hx2' : 2 ≤ x := le_of_not_gt hx2
  let L : ℕ := ⌊Real.log x / Real.log 2⌋₊
  have hsplit :
      (∑ k ∈ Icc 2 L, Chebyshev.theta (x ^ ((1 : ℝ) / k))) ≤
        Chebyshev.theta (Real.sqrt x) +
          ∑ k ∈ Icc 3 L, Chebyshev.theta (x ^ ((1 : ℝ) / k)) := by
    have hs : Icc 2 L ⊆ insert 2 (Icc 3 L) := by
      intro k hk
      obtain ⟨hk2, hkL⟩ := mem_Icc.mp hk
      by_cases hk : k = 2
      · simp [hk]
      · exact mem_insert_of_mem (mem_Icc.mpr ⟨by omega, hkL⟩)
    have hh := sum_le_sum_of_subset_of_nonneg hs
      (fun k _ _ => Chebyshev.theta_nonneg (x ^ ((1 : ℝ) / k)))
    simpa [sum_insert, Real.sqrt_eq_rpow] using hh
  have htail :
      (∑ k ∈ Icc 3 L, Chebyshev.theta (x ^ ((1 : ℝ) / k))) ≤
        (Real.log x / Real.log 2) * (Real.log 4 * x ^ ((1 : ℝ) / 3)) := by
    calc
      _ ≤ ∑ k ∈ Icc 3 L, Real.log 4 * x ^ ((1 : ℝ) / 3) := by
        apply sum_le_sum
        intro k hk
        apply (Chebyshev.theta_le_log4_mul_x (Real.rpow_nonneg hx0 _)).trans
        apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num))
        apply Real.rpow_le_rpow_of_exponent_le hx
        have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
        exact one_div_le_one_div_of_le (by norm_num) hk3
      _ ≤ (L : ℝ) * (Real.log 4 * x ^ ((1 : ℝ) / 3)) := by
        simp only [sum_const, Nat.card_Icc, nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast (show L + 1 - 3 ≤ L by omega)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact Nat.floor_le (div_nonneg (Real.log_nonneg hx) hlog2.le)
  have htail' :
      (Real.log x / Real.log 2) * (Real.log 4 * x ^ ((1 : ℝ) / 3)) ≤
        12 * Real.sqrt x := by
    calc
      _ = 2 * Real.log x * x ^ ((1 : ℝ) / 3) := by rw [hlog4]; field
      _ ≤ 2 * (x ^ ((1 : ℝ) / 6) / ((1 : ℝ) / 6)) *
          x ^ ((1 : ℝ) / 3) := by
        gcongr
        exact Real.log_le_rpow_div hx0 (by norm_num)
      _ = 12 * (x ^ ((1 : ℝ) / 6) * x ^ ((1 : ℝ) / 3)) := by ring
      _ = 12 * Real.sqrt x := by
        rw [← Real.rpow_add hxpos, Real.sqrt_eq_rpow]
        norm_num
  rw [Chebyshev.psi_eq_theta_add_sum_theta hx2', add_sub_cancel_left]
  change (∑ k ∈ Icc 2 L, Chebyshev.theta (x ^ ((1 : ℝ) / k))) ≤ _
  calc
    _ ≤ Chebyshev.theta (Real.sqrt x) +
        ∑ k ∈ Icc 3 L, Chebyshev.theta (x ^ ((1 : ℝ) / k)) := hsplit
    _ ≤ Real.log 4 * Real.sqrt x + 12 * Real.sqrt x :=
      add_le_add (Chebyshev.theta_le_log4_mul_x (Real.sqrt_nonneg x))
        (htail.trans htail')
    _ = _ := by ring

/-- A sharper `O_α(√N log N)` prime-power error bound. -/
theorem prime_power_error_bound_sharp {α : ℝ} (hα : 1 ≤ α) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ mangoldtCorrelation α N - primeCorrelation α N ∧
    mangoldtCorrelation α N - primeCorrelation α N ≤
      (Real.log 4 + 12) *
        (Real.log (α * N) * Real.sqrt N + Real.log N * Real.sqrt (α * N)) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hY : (1 : ℝ) ≤ α * N := by nlinarith
  refine ⟨sub_nonneg.mpr (primeCorrelation_le α N), ?_⟩
  apply (correlation_sub_le_psi_sub_theta hα hN).trans
  calc
    _ ≤ Real.log (α * N) * ((Real.log 4 + 12) * Real.sqrt N) +
        Real.log N * ((Real.log 4 + 12) * Real.sqrt (α * N)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (psi_sub_theta_le_sqrt hN') (Real.log_nonneg hY))
        (mul_le_mul_of_nonneg_left (psi_sub_theta_le_sqrt hY) (Real.log_nonneg hN'))
    _ = _ := by ring

#print axioms psi_sub_theta_le_sqrt
#print axioms prime_power_error_bound_sharp

end Erdos972PrimePowerError
