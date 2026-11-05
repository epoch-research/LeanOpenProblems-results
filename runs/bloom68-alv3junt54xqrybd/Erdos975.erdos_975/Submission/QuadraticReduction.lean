import Submission.OverlapEstimate
import Submission.RootReciprocalAverage

/-!
# Conditional quadratic divisor averages

The linear root-count mean is kept as an explicit hypothesis throughout this
module. A quadratic upper bound makes the balanced term `O(N)`. For a
residue-invariant sequence, an eventual quadratic lower bound also makes the
overlap `O(N)`, by finite summation by parts with inverse-square-root weights.
Together with the small-divisor limit this identifies the divisor-average
constant as twice the root-count mean.

No original conjecture or specification is imported.
-/

namespace Erdos975Support

open Filter Polynomial Asymptotics
open scoped Topology

/-- A finite linear root-count mean gives a uniform linear summatory bound,
including the input zero. -/
theorem rootCountSummatory_le_const_mul_of_tendsto {g : ℕ → ℕ} {κ : ℝ}
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory g N / (N : ℝ))
      atTop (𝓝 κ)) :
    ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ, rootCountSummatory g N ≤ B * (N : ℝ) := by
  obtain ⟨B, hB⟩ := hP.bddAbove_range
  refine ⟨max B 1, zero_lt_one.trans_le (le_max_right _ _), fun N ↦ ?_⟩
  by_cases hN : N = 0
  · simp [hN, rootCountSummatory]
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hN
  exact (div_le_iff₀ hNpos).mp
    ((hB (Set.mem_range_self N)).trans (le_max_left _ _))

/-- Every balanced divisor of a quadratically bounded value at input `n ≤ N`
lies in the common interval `N < q ≤ 4 K N`. -/
lemma balancedDivisor_mem_Ioc_of_quadratic_upper {g : ℕ → ℕ} {K N n q : ℕ}
    (hupper : ∀ n : ℕ, g n ≤ K * (n + 1) ^ 2) (hN : 1 ≤ N) (hn : n ≤ N)
    (hq : q ∈ (g n).divisors.filter (fun q ↦ N < q ∧ N < g n / q)) :
    q ∈ Finset.Ioc N (4 * K * N) := by
  obtain ⟨hqd, hqN, hcomp⟩ := Finset.mem_filter.mp hq
  have hval : g n ≤ (4 * K * N) * N := by
    calc
      g n ≤ K * (n + 1) ^ 2 := hupper n
      _ ≤ K * (2 * N) ^ 2 :=
        Nat.mul_le_mul_left K (Nat.pow_le_pow_left (by omega) 2)
      _ = (4 * K * N) * N := by ring
  have hmul : q * N ≤ (4 * K * N) * N := by
    calc
      q * N ≤ q * (g n / q) := Nat.mul_le_mul_left q hcomp.le
      _ = g n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hqd)
      _ ≤ (4 * K * N) * N := hval
  exact Finset.mem_Ioc.mpr ⟨hqN, Nat.le_of_mul_le_mul_right hmul (by omega)⟩

/-- Interchanging the input and divisor sums bounds the balanced term by a
single summatory root count. Positivity and periodicity are not needed here:
`q > N` puts the whole input interval inside one residue range. -/
theorem balancedAlong_le_rootCountSummatory_of_quadratic_upper
    {g : ℕ → ℕ} {K : ℕ} (hupper : ∀ n : ℕ, g n ≤ K * (n + 1) ^ 2)
    (N : ℕ) (hN : 1 ≤ N) :
    balancedAlong g N ≤ rootCountSummatory g (4 * K * N) := by
  have hIic : Finset.Iic N = Finset.range (N + 1) := by
    ext n
    simp only [Finset.mem_Iic, Finset.mem_range]
    omega
  have hpoint (n : ℕ) (hn : n ∈ Finset.Iic N) :
      balancedDivisorCount (g n) N ≤
        ((Finset.Ioc N (4 * K * N)).filter (fun q ↦ q ∣ g n)).card := by
    apply Finset.card_le_card
    intro q hq
    exact Finset.mem_filter.mpr
      ⟨balancedDivisor_mem_Ioc_of_quadratic_upper hupper hN (Finset.mem_Iic.mp hn) hq,
        Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hq).1⟩
  calc
    balancedAlong g N ≤ ∑ n ∈ Finset.Iic N,
        (((Finset.Ioc N (4 * K * N)).filter (fun q ↦ q ∣ g n)).card : ℝ) := by
      exact Finset.sum_le_sum fun n hn ↦ by exact_mod_cast hpoint n hn
    _ = ∑ q ∈ Finset.Ioc N (4 * K * N),
        (rootCountInRange g (N + 1) q : ℝ) := by
      simp only [← Finset.sum_boole]
      rw [Finset.sum_comm, hIic]
      simp only [rootCountInRange, Finset.sum_boole]
    _ ≤ ∑ q ∈ Finset.Ioc N (4 * K * N), (rootCount g q : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hNq : N + 1 ≤ q := by
        have := (Finset.mem_Ioc.mp hq).1
        omega
      exact_mod_cast (show rootCountInRange g (N + 1) q ≤ rootCount g q from
        Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.range_mono hNq)))
    _ ≤ rootCountSummatory g (4 * K * N) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        obtain ⟨hqN, hqK⟩ := Finset.mem_Ioc.mp hq
        exact Finset.mem_Ioc.mpr ⟨by omega, hqK⟩
      · intro q _ _
        exact Nat.cast_nonneg _

/-- An eventual `O(N)` upper bound for a nonnegative sequence is negligible
under the normalization `N log N`. -/
lemma tendsto_div_mul_log_of_eventual_linear_bound {u : ℕ → ℝ} {A : ℝ}
    (hu : ∀ N : ℕ, 0 ≤ u N)
    (hA : ∀ᶠ N : ℕ in atTop, u N ≤ A * (N : ℝ)) :
    Tendsto (fun N : ℕ ↦ u N / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (tendsto_log_nat_atTop.const_div_atTop A)
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    exact div_nonneg (hu N)
      (mul_nonneg (Nat.cast_nonneg _) (Real.log_pos hN1).le)
  · filter_upwards [hA, eventually_ge_atTop 2] with N hAN hN
    have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    have hNpos : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans hN1
    have hden : (0 : ℝ) < (N : ℝ) * Real.log (N : ℝ) :=
      mul_pos hNpos (Real.log_pos hN1)
    calc
      u N / ((N : ℝ) * Real.log (N : ℝ)) ≤
          (A * (N : ℝ)) / ((N : ℝ) * Real.log (N : ℝ)) :=
        div_le_div_of_nonneg_right hAN hden.le
      _ = A / Real.log (N : ℝ) := by
        rw [mul_comm A]
        exact mul_div_mul_left A (Real.log (N : ℝ)) hNpos.ne'

/-- Quadratic upper growth and a finite linear root-count mean make the
balanced correction vanish. This statement does not require positivity or
residue invariance of the sequence. -/
theorem tendsto_balancedAlong_div_mul_log_of_quadratic_upper
    {g : ℕ → ℕ} {κ : ℝ}
    (hupper : ∃ K : ℕ, ∀ n : ℕ, g n ≤ K * (n + 1) ^ 2)
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory g N / (N : ℝ))
      atTop (𝓝 κ)) :
    Tendsto (fun N : ℕ ↦ balancedAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := hupper
  obtain ⟨B, _hB, hbound⟩ := rootCountSummatory_le_const_mul_of_tendsto hP
  apply tendsto_div_mul_log_of_eventual_linear_bound
    (A := B * (4 * (K : ℝ))) (balancedAlong_nonneg g)
  filter_upwards [eventually_ge_atTop 1] with N hN
  calc
    balancedAlong g N ≤ rootCountSummatory g (4 * K * N) :=
      balancedAlong_le_rootCountSummatory_of_quadratic_upper hK N hN
    _ ≤ B * ((4 * K * N : ℕ) : ℝ) := hbound _
    _ = (B * (4 * (K : ℝ))) * (N : ℝ) := by push_cast; ring

/-- Finite summation-by-parts comparison: prefix-sum domination is preserved
by nonnegative decreasing weights on the positive natural numbers. -/
lemma sum_Ioc_mul_le_of_prefix_sum_le {a w : ℕ → ℝ} {B : ℝ}
    (hbound : ∀ N : ℕ, (∑ q ∈ Finset.Ioc 0 N, a q) ≤ B * (N : ℝ))
    (hw : ∀ n : ℕ, 1 ≤ n → w (n + 1) ≤ w n)
    (hw0 : ∀ n : ℕ, 0 ≤ w n) (N : ℕ) :
    (∑ q ∈ Finset.Ioc 0 N, a q * w q) ≤ B * ∑ q ∈ Finset.Ioc 0 N, w q := by
  have haux (N : ℕ) :
      (∑ q ∈ Finset.Ioc 0 N, a q * w q) ≤
        B * (∑ q ∈ Finset.Ioc 0 N, w q) +
          ((∑ q ∈ Finset.Ioc 0 N, a q) - B * (N : ℝ)) * w N := by
    induction N with
    | zero => simp
    | succ N ih =>
      have hstep :
          ((∑ q ∈ Finset.Ioc 0 N, a q) - B * (N : ℝ)) *
            (w N - w (N + 1)) ≤ 0 := by
        by_cases hN : N = 0
        · simp [hN]
        · exact mul_nonpos_of_nonpos_of_nonneg
            (sub_nonpos.mpr (hbound N))
            (sub_nonneg.mpr (hw N (Nat.one_le_iff_ne_zero.mpr hN)))
      simp only [Finset.sum_Ioc_succ_top (Nat.zero_le N),
        Nat.cast_add, Nat.cast_one]
      nlinarith only [ih, hstep]
  exact (haux N).trans (by
    have hlast := mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hbound N)) (hw0 N)
    linarith)

/-- The unweighted inverse-square-root sum is bounded by a telescoping
square-root difference. -/
lemma sum_Ioc_inv_sqrt_le (N : ℕ) :
    (∑ q ∈ Finset.Ioc 0 N, 1 / Real.sqrt (q : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hspos : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.mpr hpos
    have hterm : 1 / Real.sqrt ((N : ℝ) + 1) ≤
        2 * (Real.sqrt ((N : ℝ) + 1) - Real.sqrt (N : ℝ)) := by
      apply (div_le_iff₀ hspos).mpr
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg N), Real.sq_sqrt hpos.le,
        sq_nonneg (Real.sqrt ((N : ℝ) + 1) - Real.sqrt (N : ℝ))]
    simp only [Finset.sum_Ioc_succ_top (Nat.zero_le N),
      Nat.cast_add, Nat.cast_one]
    linarith

/-- Abel's finite comparison and the telescoping square-root estimate give the
weighted root-count bound needed for quadratic overlap. -/
theorem rootCount_sqrt_weighted_sum_le {g : ℕ → ℕ} {B : ℝ}
    (hB : 0 ≤ B) (hP : ∀ N : ℕ, rootCountSummatory g N ≤ B * (N : ℝ))
    (N : ℕ) :
    (∑ q ∈ Finset.Ioc 0 N, (rootCount g q : ℝ) / Real.sqrt (q : ℝ)) ≤
      2 * B * Real.sqrt (N : ℝ) := by
  have hcomp := sum_Ioc_mul_le_of_prefix_sum_le
    (a := fun q ↦ (rootCount g q : ℝ))
    (w := fun q ↦ 1 / Real.sqrt (q : ℝ)) hP
    (fun n hn ↦ one_div_le_one_div_of_le
      (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega)))
      (Real.sqrt_le_sqrt (by push_cast; linarith)))
    (fun n ↦ by positivity) N
  simp only [mul_one_div] at hcomp
  calc
    (∑ q ∈ Finset.Ioc 0 N, (rootCount g q : ℝ) / Real.sqrt (q : ℝ)) ≤
        B * ∑ q ∈ Finset.Ioc 0 N, 1 / Real.sqrt (q : ℝ) := hcomp
    _ ≤ B * (2 * Real.sqrt (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_Ioc_inv_sqrt_le N) hB
    _ = 2 * B * Real.sqrt (N : ℝ) := by ring

/-- The overlap can be summed first over its small factor. The divisibility
and sublevel conditions are only an upper bound, so zero values are allowed. -/
lemma overlapAlong_le_sum_sublevel_roots (g : ℕ → ℕ) (N : ℕ) :
    overlapAlong g N ≤ ∑ q ∈ Finset.Ioc 0 N,
      (((Finset.Iic N).filter (fun n ↦ q ∣ g n ∧ g n ≤ q * N)).card : ℝ) := by
  have hpoint (n : ℕ) : overlapDivisorCount (g n) N ≤
      ((Finset.Ioc 0 N).filter (fun q ↦ q ∣ g n ∧ g n ≤ q * N)).card := by
    apply Finset.card_le_card
    intro q hq
    obtain ⟨hqd, hqN, hcomp⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨Nat.pos_of_mem_divisors hqd, hqN⟩,
        Nat.dvd_of_mem_divisors hqd, ?_⟩
    calc
      g n = q * (g n / q) := (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hqd)).symm
      _ ≤ q * N := Nat.mul_le_mul_left q hcomp
  calc
    overlapAlong g N ≤ ∑ n ∈ Finset.Iic N,
        (((Finset.Ioc 0 N).filter (fun q ↦ q ∣ g n ∧ g n ≤ q * N)).card : ℝ) := by
      exact Finset.sum_le_sum fun n _ ↦ by exact_mod_cast hpoint n
    _ = _ := by
      simp only [← Finset.sum_boole]
      rw [Finset.sum_comm]

/-- A useful exact algebraic identity for the square-root weight. -/
lemma mul_sqrt_div_eq_div_sqrt (a : ℝ) {q : ℝ} (hq : 0 < q) :
    a * Real.sqrt q / q = a / Real.sqrt q := by
  apply (div_eq_div_iff hq.ne' (Real.sqrt_pos.mpr hq).ne').mpr
  rw [mul_assoc, ← pow_two, Real.sq_sqrt hq.le]

/-- Quadratic lower growth restricts the roots counted by the overlap to a
short initial interval. Its finite exceptional segment costs only `M + 2`
full residue blocks per modulus. -/
lemma quadratic_sublevel_root_card_le {g : ℕ → ℕ} {C : ℝ} {M : ℕ}
    (hC : 0 < C)
    (hg : ∀ n : ℕ, M ≤ n → (n : ℝ) ^ 2 ≤ C * (g n : ℝ))
    (q N : ℕ) (hq : 0 < q)
    (hmod : ∀ n : ℕ, q ∣ g n ↔ q ∣ g (n % q)) :
    (((Finset.Iic N).filter (fun n ↦ q ∣ g n ∧ g n ≤ q * N)).card : ℝ) ≤
      (rootCount g q : ℝ) *
        (Real.sqrt (C * (N : ℝ)) / Real.sqrt (q : ℝ) + (M : ℝ) + 2) := by
  let A : ℝ := Real.sqrt (C * (N : ℝ))
  let R : ℝ := (M : ℝ) + A * Real.sqrt (q : ℝ)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hR : 0 ≤ R := by dsimp [R, A]; positivity
  have hs : (Finset.Iic N).filter (fun n ↦ q ∣ g n ∧ g n ≤ q * N) ⊆
      (Finset.range (Nat.floor R + 1)).filter (fun n ↦ q ∣ g n) := by
    intro n hn
    obtain ⟨_hnN, hqn, hval⟩ := Finset.mem_filter.mp hn
    have hnR : (n : ℝ) ≤ R := by
      by_cases hMn : M ≤ n
      · have hvalR : (g n : ℝ) ≤ (q : ℝ) * (N : ℝ) := by exact_mod_cast hval
        have hsq : (n : ℝ) ^ 2 ≤ (C * (N : ℝ)) * (q : ℝ) := by
          calc
            (n : ℝ) ^ 2 ≤ C * (g n : ℝ) := hg n hMn
            _ ≤ C * ((q : ℝ) * (N : ℝ)) :=
              mul_le_mul_of_nonneg_left hvalR hC.le
            _ = (C * (N : ℝ)) * (q : ℝ) := by ring
        have hnA := (Real.le_sqrt (Nat.cast_nonneg n) (by positivity)).mpr hsq
        rw [Real.sqrt_mul (mul_nonneg hC.le (Nat.cast_nonneg N))] at hnA
        dsimp [R, A]
        linarith [Nat.cast_nonneg (α := ℝ) M]
      · have hnM : (n : ℝ) ≤ (M : ℝ) := by
          exact_mod_cast (show n ≤ M by omega)
        exact hnM.trans (le_add_of_nonneg_right (by dsimp [A]; positivity))
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor hnR)), hqn⟩
  have hlen : ((Nat.floor R + 1 : ℕ) : ℝ) ≤
      (M : ℝ) + 1 + A * Real.sqrt (q : ℝ) := by
    have hf := Nat.floor_le hR
    dsimp [R] at hf
    push_cast
    linarith
  have hlenDiv : ((Nat.floor R + 1 : ℕ) : ℝ) / (q : ℝ) ≤
      (M : ℝ) + 1 + A / Real.sqrt (q : ℝ) := by
    calc
      ((Nat.floor R + 1 : ℕ) : ℝ) / (q : ℝ) ≤
          ((M : ℝ) + 1 + A * Real.sqrt (q : ℝ)) / (q : ℝ) :=
        div_le_div_of_nonneg_right hlen hqpos.le
      _ = ((M : ℝ) + 1) / (q : ℝ) + A / Real.sqrt (q : ℝ) := by
        rw [add_div, mul_sqrt_div_eq_div_sqrt A hqpos]
      _ ≤ (M : ℝ) + 1 + A / Real.sqrt (q : ℝ) := by
        refine add_le_add ?_ le_rfl
        apply (div_le_iff₀ hqpos).mpr
        nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have hcount : (rootCountInRange g (Nat.floor R + 1) q : ℝ) ≤
      (((Nat.floor R + 1 : ℕ) : ℝ) / (q : ℝ) + 1) * (rootCount g q : ℝ) := by
    have he := (abs_le.mp (rootCountInRange_error_le hq hmod (Nat.floor R + 1))).2
    rw [add_mul, div_mul_eq_mul_div, one_mul]
    linarith
  calc
    (((Finset.Iic N).filter (fun n ↦ q ∣ g n ∧ g n ≤ q * N)).card : ℝ) ≤
        (rootCountInRange g (Nat.floor R + 1) q : ℝ) := by
      exact_mod_cast Finset.card_le_card hs
    _ ≤ (((Nat.floor R + 1 : ℕ) : ℝ) / (q : ℝ) + 1) * (rootCount g q : ℝ) := hcount
    _ ≤ ((M : ℝ) + 1 + A / Real.sqrt (q : ℝ) + 1) * (rootCount g q : ℝ) :=
      mul_le_mul_of_nonneg_right (add_le_add hlenDiv (le_refl 1)) (Nat.cast_nonneg _)
    _ = (rootCount g q : ℝ) *
        (Real.sqrt (C * (N : ℝ)) / Real.sqrt (q : ℝ) + (M : ℝ) + 2) := by
      dsimp [A]
      ring

/-- Eventual quadratic lower growth, residue invariance, and a finite root-count
mean give a uniform `O(N)` overlap estimate. No quadratic upper bound or
positivity of `g` is required for this correction term. -/
theorem overlapAlong_le_const_mul_of_quadratic_lower {g : ℕ → ℕ} {κ C : ℝ}
    (hC : 0 < C)
    (hmod : ∀ q : ℕ, 0 < q → ∀ n : ℕ, q ∣ g n ↔ q ∣ g (n % q))
    (hg : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 ≤ C * (g n : ℝ))
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory g N / (N : ℝ))
      atTop (𝓝 κ)) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, overlapAlong g N ≤ A * (N : ℝ) := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp hg
  obtain ⟨B, hB, hbound⟩ := rootCountSummatory_le_const_mul_of_tendsto hP
  refine ⟨B * (2 * Real.sqrt C + (M : ℝ) + 2), by positivity, fun N ↦ ?_⟩
  calc
    overlapAlong g N ≤ ∑ q ∈ Finset.Ioc 0 N,
        (((Finset.Iic N).filter (fun n ↦ q ∣ g n ∧ g n ≤ q * N)).card : ℝ) :=
      overlapAlong_le_sum_sublevel_roots g N
    _ ≤ ∑ q ∈ Finset.Ioc 0 N, (rootCount g q : ℝ) *
        (Real.sqrt (C * (N : ℝ)) / Real.sqrt (q : ℝ) + (M : ℝ) + 2) := by
      apply Finset.sum_le_sum
      intro q hq
      have hq0 := (Finset.mem_Ioc.mp hq).1
      exact quadratic_sublevel_root_card_le hC hM q N hq0 (hmod q hq0)
    _ = Real.sqrt (C * (N : ℝ)) *
        (∑ q ∈ Finset.Ioc 0 N, (rootCount g q : ℝ) / Real.sqrt (q : ℝ)) +
          ((M : ℝ) + 2) * rootCountSummatory g N := by
      unfold rootCountSummatory
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ Real.sqrt (C * (N : ℝ)) * (2 * B * Real.sqrt (N : ℝ)) +
        ((M : ℝ) + 2) * (B * (N : ℝ)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (rootCount_sqrt_weighted_sum_le hB.le hbound N)
          (Real.sqrt_nonneg _))
        (mul_le_mul_of_nonneg_left (hbound N) (by positivity))
    _ = (B * (2 * Real.sqrt C + (M : ℝ) + 2)) * (N : ℝ) := by
      rw [Real.sqrt_mul hC.le]
      calc
        Real.sqrt C * Real.sqrt (N : ℝ) * (2 * B * Real.sqrt (N : ℝ)) +
            ((M : ℝ) + 2) * (B * (N : ℝ)) =
          B * (2 * Real.sqrt C * (Real.sqrt (N : ℝ)) ^ 2 +
            ((M : ℝ) + 2) * (N : ℝ)) := by ring
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]; ring

/-- The overlap correction vanishes for quadratically growing residue-invariant
sequences with a finite linear root-count mean. -/
theorem tendsto_overlapAlong_div_mul_log_of_quadratic_lower
    {g : ℕ → ℕ} {κ C : ℝ} (hC : 0 < C)
    (hmod : ∀ q : ℕ, 0 < q → ∀ n : ℕ, q ∣ g n ↔ q ∣ g (n % q))
    (hg : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 ≤ C * (g n : ℝ))
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory g N / (N : ℝ))
      atTop (𝓝 κ)) :
    Tendsto (fun N : ℕ ↦ overlapAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 0) := by
  obtain ⟨A, _hA, hbound⟩ := overlapAlong_le_const_mul_of_quadratic_lower hC hmod hg hP
  exact tendsto_div_mul_log_of_eventual_linear_bound (overlapAlong_nonneg g)
    (Eventually.of_forall hbound)

/-- The lower-growth convention `c n² ≤ g n`, with positive `c`, gives the
same vanishing overlap estimate. -/
theorem tendsto_overlapAlong_div_mul_log_of_quadratic_growth
    {g : ℕ → ℕ} {κ : ℝ}
    (hmod : ∀ q : ℕ, 0 < q → ∀ n : ℕ, q ∣ g n ↔ q ∣ g (n % q))
    (hlower : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ 2 ≤ (g n : ℝ))
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory g N / (N : ℝ))
      atTop (𝓝 κ)) :
    Tendsto (fun N : ℕ ↦ overlapAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 0) := by
  obtain ⟨c, hc, hg⟩ := hlower
  apply tendsto_overlapAlong_div_mul_log_of_quadratic_lower
    (C := 1 / c) (one_div_pos.mpr hc) hmod ?_ hP
  filter_upwards [hg] with n hn
  have hdiv : (n : ℝ) ^ 2 ≤ (g n : ℝ) / c :=
    (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hn)
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using hdiv

/-- A positive residue-invariant sequence with two-sided quadratic growth has
divisor-average constant `2 κ`, conditional on its linear root-count mean.
There is no sign assumption on `κ` for this limit statement. -/
theorem tendsto_divisorAlong_of_quadratic_growth {g : ℕ → ℕ} {κ : ℝ}
    (hg : ∀ n : ℕ, 0 < g n)
    (hmod : ∀ q : ℕ, 0 < q → ∀ n : ℕ, q ∣ g n ↔ q ∣ g (n % q))
    (hupper : ∃ K : ℕ, ∀ n : ℕ, g n ≤ K * (n + 1) ^ 2)
    (hlower : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ 2 ≤ (g n : ℝ))
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory g N / (N : ℝ))
      atTop (𝓝 κ)) :
    Tendsto (fun N : ℕ ↦ divisorAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 (2 * κ)) := by
  have hs := tendsto_smallAlong_of_linear_rootCount hg hmod hP
  have ho := tendsto_overlapAlong_div_mul_log_of_quadratic_growth hmod hlower hP
  apply (balanced_limit_iff (c := 2 * κ) hs ho).mpr
  simpa only [sub_self] using
    tendsto_balancedAlong_div_mul_log_of_quadratic_upper hupper hP

/-- In particular the conditional divisor-average constant is positive when
the root-count mean is positive; it can be chosen to be exactly `2 κ`. -/
theorem exists_pos_divisorAlong_limit_of_quadratic_growth {g : ℕ → ℕ} {κ : ℝ}
    (hg : ∀ n : ℕ, 0 < g n)
    (hmod : ∀ q : ℕ, 0 < q → ∀ n : ℕ, q ∣ g n ↔ q ∣ g (n % q))
    (hupper : ∃ K : ℕ, ∀ n : ℕ, g n ≤ K * (n + 1) ^ 2)
    (hlower : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ 2 ≤ (g n : ℝ))
    (hκ : 0 < κ)
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory g N / (N : ℝ))
      atTop (𝓝 κ)) :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun N : ℕ ↦ divisorAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
        atTop (𝓝 c) :=
  ⟨2 * κ, by positivity, tendsto_divisorAlong_of_quadratic_growth hg hmod hupper hlower hP⟩

/-- The leading-term asymptotic gives a uniform natural quadratic upper bound
for every integer polynomial of natural degree at most two. The finitely many
inputs before the asymptotic bound are absorbed into the natural constant. -/
theorem polynomialAbsValue_quadratic_upper_bound (f : ℤ[X])
    (hdeg : f.natDegree ≤ 2) :
    ∃ K : ℕ, ∀ n : ℕ, polynomialAbsValue f n ≤ K * (n + 1) ^ 2 := by
  let P : ℝ[X] := f.map (Int.castRingHom ℝ)
  have hdegP : P.natDegree ≤ 2 := by
    dsimp [P]
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    exact hdeg
  obtain ⟨D, hD, hbound⟩ := P.isEquivalent_atTop_lead.isBigO.exists_pos
  let A : ℝ := D * |P.leadingCoeff|
  have hA : 0 ≤ A := mul_nonneg hD.le (abs_nonneg _)
  have hupperR : ∀ᶠ x : ℝ in atTop, |P.eval x| ≤ A * (x + 1) ^ 2 := by
    filter_upwards [hbound.bound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hx0 : 0 ≤ x := zero_le_one.trans hx1
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx0] at hx
    calc
      |P.eval x| ≤ D * (|P.leadingCoeff| * x ^ P.natDegree) := hx
      _ = A * x ^ P.natDegree := by dsimp [A]; ring
      _ ≤ A * x ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1 hdegP) hA
      _ ≤ A * (x + 1) ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hA
  have hnat : ∀ᶠ n : ℕ in atTop,
      (polynomialAbsValue f n : ℝ) ≤ A * ((n : ℝ) + 1) ^ 2 := by
    have hn := (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually hupperR
    simpa only [polynomialAbsValue_cast_real, P] using hn
  obtain ⟨M, hM⟩ := eventually_atTop.mp hnat
  let K : ℕ := Nat.ceil A + ∑ k ∈ Finset.range M, polynomialAbsValue f k
  have hKreal : A ≤ (K : ℝ) := by
    apply (Nat.le_ceil A).trans
    exact_mod_cast (show Nat.ceil A ≤ K from Nat.le_add_right _ _)
  refine ⟨K, fun n ↦ ?_⟩
  by_cases hMn : M ≤ n
  · have hlarge : (polynomialAbsValue f n : ℝ) ≤ (K : ℝ) * ((n : ℝ) + 1) ^ 2 :=
      (hM n hMn).trans (mul_le_mul_of_nonneg_right hKreal (sq_nonneg _))
    exact_mod_cast hlarge
  · have hsmall : polynomialAbsValue f n ≤
        ∑ k ∈ Finset.range M, polynomialAbsValue f k :=
      Finset.single_le_sum (fun k _ ↦ Nat.zero_le _)
        (Finset.mem_range.mpr (Nat.lt_of_not_ge hMn))
    calc
      polynomialAbsValue f n ≤ ∑ k ∈ Finset.range M, polynomialAbsValue f k := hsmall
      _ ≤ K := Nat.le_add_left _ _
      _ ≤ K * (n + 1) ^ 2 := by
        simpa only [mul_one] using
          Nat.mul_le_mul_left K (show 1 ≤ (n + 1) ^ 2 by nlinarith)

/-- Every integer polynomial of degree at least two has eventual quadratic
absolute growth. This follows from the equivalence to its leading monomial;
neither irreducibility nor eventual positivity is used. -/
theorem polynomialAbsValue_eventual_quadratic_growth (f : ℤ[X])
    (hdeg : 2 ≤ f.natDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 ≤ C * (polynomialAbsValue f n : ℝ) := by
  let P : ℝ[X] := f.map (Int.castRingHom ℝ)
  have hdegP : 2 ≤ P.natDegree := by
    dsimp [P]
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    exact hdeg
  have hf : f ≠ 0 := by
    intro hf
    simp [hf] at hdeg
  have hlc : (1 : ℝ) ≤ |P.leadingCoeff| := by
    dsimp [P]
    rw [Polynomial.leadingCoeff_map_of_injective Int.cast_injective]
    have hn : 1 ≤ f.leadingCoeff.natAbs := by
      have := Int.natAbs_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hf)
      omega
    have hh : (1 : ℝ) ≤ (f.leadingCoeff.natAbs : ℝ) := by exact_mod_cast hn
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
  obtain ⟨C, hC, hbound⟩ := P.isEquivalent_atTop_lead.isBigO_symm.exists_pos
  have hgrowth : ∀ᶠ x : ℝ in atTop, x ^ 2 ≤ C * |P.eval x| := by
    filter_upwards [hbound.bound, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hx0 : 0 ≤ x := zero_le_one.trans hx1
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx0] at hx
    calc
      x ^ 2 ≤ x ^ P.natDegree := pow_le_pow_right₀ hx1 hdegP
      _ ≤ |P.leadingCoeff| * x ^ P.natDegree := by
        nlinarith [pow_nonneg hx0 P.natDegree]
      _ ≤ C * |P.eval x| := hx
  refine ⟨C, hC, ?_⟩
  have hn := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually hgrowth
  simpa only [polynomialAbsValue_cast_real, P] using hn

/-- The preceding leading-term bound in the lower-growth convention used by
the generic divisor-average theorem. -/
theorem polynomialAbsValue_eventual_quadratic_lower_bound (f : ℤ[X])
    (hdeg : 2 ≤ f.natDegree) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ^ 2 ≤ (polynomialAbsValue f n : ℝ) := by
  obtain ⟨C, hC, hg⟩ := polynomialAbsValue_eventual_quadratic_growth f hdeg
  refine ⟨1 / C, one_div_pos.mpr hC, ?_⟩
  filter_upwards [hg] with n hn
  have hdiv : (n : ℝ) ^ 2 / C ≤ (polynomialAbsValue f n : ℝ) :=
    (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hn)
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_one, mul_comm] using hdiv

/-- For an irreducible quadratic, a linear root-count mean alone determines
the natural-cutoff divisor average of its absolute values. -/
theorem tendsto_polynomial_divisorAlong_of_quadratic_root_mean
    (f : ℤ[X]) (hf : Irreducible f) (hdeg : f.natDegree = 2) {κ : ℝ}
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory (polynomialAbsValue f) N / (N : ℝ))
      atTop (𝓝 κ)) :
    Tendsto (fun N : ℕ ↦ divisorAlong (polynomialAbsValue f) N /
      ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 (2 * κ)) := by
  exact tendsto_divisorAlong_of_quadratic_growth
    (polynomialAbsValue_pos f hf (by omega)) (polynomialAbsValue_mod_dvd f)
    (polynomialAbsValue_quadratic_upper_bound f (by omega))
    (polynomialAbsValue_eventual_quadratic_lower_bound f (by omega)) hP

/-- Transfer the conditional quadratic average to the original floor convention
and real cutoffs, under eventual positivity on integer inputs. -/
theorem tendsto_flooredPolynomialSum_of_quadratic_root_mean
    (f : ℤ[X]) (hf : Irreducible f) (hdeg : f.natDegree = 2)
    (hpos : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) {κ : ℝ}
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory (polynomialAbsValue f) N / (N : ℝ))
      atTop (𝓝 κ)) :
    Tendsto (fun x : ℝ ↦ flooredPolynomialSum f x / (x * Real.log x))
      atTop (𝓝 (2 * κ)) :=
  (flooredPolynomialSum_limit_iff f hpos (2 * κ)).mpr
    (tendsto_polynomial_divisorAlong_of_quadratic_root_mean f hf hdeg hP)

/-- The full quadratic divisor-average conclusion, conditional only on a
positive linear root-count mean in addition to the polynomial hypotheses.
The displayed sum uses exactly the original floor convention, without
importing the original conjecture. Its constant is `2 κ` for the supplied mean. -/
theorem quadratic_divisor_average_of_root_mean
    (f : ℤ[X]) (hf : Irreducible f) (hdeg : f.natDegree = 2)
    (hpos : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n)
    (hmean : ∃ κ : ℝ, 0 < κ ∧
      Tendsto (fun N : ℕ ↦ rootCountSummatory (polynomialAbsValue f) N / (N : ℝ))
        atTop (𝓝 κ)) :
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun x : ℝ ↦
      (∑ n ∈ Finset.Iic (Nat.floor x),
        (ArithmeticFunction.sigma0 (Nat.floor (f.eval (n : ℤ))) : ℝ)) /
          (x * Real.log x)) atTop (𝓝 c) := by
  obtain ⟨κ, hκ, hP⟩ := hmean
  refine ⟨2 * κ, by positivity, ?_⟩
  exact tendsto_flooredPolynomialSum_of_quadratic_root_mean f hf hdeg hpos hP

end Erdos975Support
