import Submission.BalancedReduction

/-!
# Small-divisor averages from residue root counts

For a positive sequence `g` whose divisibility predicates depend only on residues,
small-divisor counts can be summed first over the divisor. A complete-block and
remainder decomposition gives an error at most the summatory residue root count.
Consequently a logarithmic root-reciprocal limit and an eventual linear bound on
the root-count summatory function imply the same normalized small-divisor limit.
A finite limit of the root-count summatory function divided by `N` suffices.

These are supporting results, not a polynomial divisor-average theorem.
-/

namespace Erdos975Support

open Filter
open scoped Topology

/-- Number of residue roots of the divisibility predicate modulo `q`.
For `q = 0` this is zero, since the range is empty. -/
def rootCount (g : ℕ → ℕ) (q : ℕ) : ℕ :=
  ((Finset.range q).filter fun r ↦ q ∣ g r).card

/-- The real root-count summatory function, over positive moduli at most `N`. -/
noncomputable def rootCountSummatory (g : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc 0 N, (rootCount g q : ℝ)

/-- The real root-reciprocal sum, over positive moduli at most `N`. -/
noncomputable def rootReciprocalSum (g : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioc 0 N, (rootCount g q : ℝ) / (q : ℝ)

/-- Number of roots in the initial interval `0 ≤ n < M`. -/
def rootCountInRange (g : ℕ → ℕ) (M q : ℕ) : ℕ :=
  ((Finset.range M).filter fun n ↦ q ∣ g n).card

/-- A sum over complete blocks of a periodic function. -/
lemma sum_range_mul_of_periodic {A : Type*} [AddCommMonoid A]
    {f : ℕ → A} {q : ℕ} (hf : Function.Periodic f q) (k : ℕ) :
    (∑ n ∈ Finset.range (k * q), f n) = k • (∑ r ∈ Finset.range q, f r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    have hshift : (∑ r ∈ Finset.range q, f (k * q + r)) =
        ∑ r ∈ Finset.range q, f r := by
      apply Finset.sum_congr rfl
      intro r _
      simpa only [Nat.cast_id, Nat.add_comm] using (hf.nat_mul k) r
    rw [hshift, succ_nsmul]

/-- A generic periodic sum splits into complete blocks and a partial block.
This also holds for `q = 0` with the usual natural division conventions. -/
lemma sum_range_div_mod_of_periodic {A : Type*} [AddCommMonoid A]
    {f : ℕ → A} {q : ℕ} (hf : Function.Periodic f q) (M : ℕ) :
    (∑ n ∈ Finset.range M, f n) =
      (M / q) • (∑ r ∈ Finset.range q, f r) +
        ∑ r ∈ Finset.range (M % q), f r := by
  have hM : M = (M / q) * q + M % q := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod M q).symm
  calc
    (∑ n ∈ Finset.range M, f n) =
        (∑ n ∈ Finset.range ((M / q) * q + M % q), f n) := by rw [← hM]
    _ = (M / q) • (∑ r ∈ Finset.range q, f r) +
        ∑ r ∈ Finset.range (M % q), f ((M / q) * q + r) := by
      rw [Finset.sum_range_add, sum_range_mul_of_periodic hf]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      simpa only [Nat.cast_id, Nat.add_comm] using (hf.nat_mul (M / q)) r

/-- Exact complete-block and remainder count for a residue-invariant predicate. -/
lemma rootCountInRange_eq_blocks {g : ℕ → ℕ} {q : ℕ}
    (hmod : ∀ n : ℕ, q ∣ g n ↔ q ∣ g (n % q)) (M : ℕ) :
    rootCountInRange g M q =
      (M / q) * rootCount g q + rootCountInRange g (M % q) q := by
  have hi : Function.Periodic (fun n : ℕ ↦ if q ∣ g n then (1 : ℕ) else 0) q := by
    intro n
    have hd : (q ∣ g (n + q)) ↔ q ∣ g n := by
      rw [hmod (n + q), Nat.add_mod_right, ← hmod n]
    simp only [hd]
  simpa only [Finset.sum_boole, Nat.cast_id, nsmul_eq_mul, rootCountInRange, rootCount]
    using sum_range_div_mod_of_periodic hi M

/-- The partial block contains no more roots than a full block. -/
lemma rootCountInRange_mod_le {g : ℕ → ℕ} {q : ℕ} (hq : 0 < q) (M : ℕ) :
    rootCountInRange g (M % q) q ≤ rootCount g q := by
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ (Finset.range_mono (Nat.mod_lt M hq).le)

/-- The periodic count differs from its real mean by at most one full root count. -/
theorem rootCountInRange_error_le {g : ℕ → ℕ} {q : ℕ} (hq : 0 < q)
    (hmod : ∀ n : ℕ, q ∣ g n ↔ q ∣ g (n % q)) (M : ℕ) :
    |(rootCountInRange g M q : ℝ) - (M : ℝ) * (rootCount g q : ℝ) / (q : ℝ)| ≤
      (rootCount g q : ℝ) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hR : (rootCountInRange g M q : ℝ) =
      ((M / q : ℕ) : ℝ) * (rootCount g q : ℝ) +
        (rootCountInRange g (M % q) q : ℝ) := by
    exact_mod_cast rootCountInRange_eq_blocks hmod M
  have hM : (M : ℝ) = ((M / q : ℕ) : ℝ) * (q : ℝ) + ((M % q : ℕ) : ℝ) := by
    exact_mod_cast (show M = (M / q) * q + M % q by
      simpa only [Nat.mul_comm] using (Nat.div_add_mod M q).symm)
  have hpartial : (rootCountInRange g (M % q) q : ℝ) ≤ (rootCount g q : ℝ) := by
    exact_mod_cast rootCountInRange_mod_le (g := g) hq M
  have hrem0 : (0 : ℝ) ≤ ((M % q : ℕ) : ℝ) * (rootCount g q : ℝ) / (q : ℝ) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hqR.le
  have hrem1 : ((M % q : ℕ) : ℝ) * (rootCount g q : ℝ) / (q : ℝ) ≤
      (rootCount g q : ℝ) := by
    apply (div_le_iff₀ hqR).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right
      (show ((M % q : ℕ) : ℝ) ≤ (q : ℝ) by exact_mod_cast (Nat.mod_lt M hq).le)
      (Nat.cast_nonneg (rootCount g q) : (0 : ℝ) ≤ _)
  have heq : (rootCountInRange g M q : ℝ) -
      (M : ℝ) * (rootCount g q : ℝ) / (q : ℝ) =
        (rootCountInRange g (M % q) q : ℝ) -
          ((M % q : ℕ) : ℝ) * (rootCount g q : ℝ) / (q : ℝ) := by
    rw [hR, hM]
    field_simp
    ring
  rw [heq]
  apply abs_le.mpr
  constructor <;> linarith
    [(Nat.cast_nonneg (rootCountInRange g (M % q) q) : (0 : ℝ) ≤ _)]

/-- For positive `m`, small divisors are exactly the positive divisibility roots
at the cutoff. Positivity excludes the exceptional divisor convention at zero. -/
lemma smallDivisorCount_eq_root_filter {m N : ℕ} (hm : 0 < m) :
    smallDivisorCount m N = ((Finset.Ioc 0 N).filter fun q ↦ q ∣ m).card := by
  unfold smallDivisorCount
  congr 1
  ext q
  constructor
  · intro h
    obtain ⟨hd, hN⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr ⟨Nat.pos_of_mem_divisors hd, hN⟩,
        Nat.dvd_of_mem_divisors hd⟩
  · intro h
    obtain ⟨hN, hd⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hd, Nat.ne_of_gt hm⟩, (Finset.mem_Ioc.mp hN).2⟩

/-- Interchange the finite divisor sum and the finite input sum.
The interval `Iic N` includes zero and therefore has length `N + 1`. -/
theorem smallAlong_eq_sum_rootCountInRange {g : ℕ → ℕ}
    (hg : ∀ n : ℕ, 0 < g n) (N : ℕ) :
    smallAlong g N =
      ∑ q ∈ Finset.Ioc 0 N, (rootCountInRange g (N + 1) q : ℝ) := by
  have hIic : Finset.Iic N = Finset.range (N + 1) := by
    ext n
    simp only [Finset.mem_Iic, Finset.mem_range]
    omega
  unfold smallAlong
  calc
    (∑ n ∈ Finset.Iic N, (smallDivisorCount (g n) N : ℝ)) =
        ∑ n ∈ Finset.Iic N, ∑ q ∈ Finset.Ioc 0 N,
          if q ∣ g n then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n _
      rw [smallDivisorCount_eq_root_filter (hg n), Finset.sum_boole]
    _ = ∑ q ∈ Finset.Ioc 0 N, ∑ n ∈ Finset.range (N + 1),
          if q ∣ g n then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm, hIic]
    _ = _ := by simp only [Finset.sum_boole, rootCountInRange]

/-- The finite small-divisor average has a remainder bounded by the summatory
root count, with the exact inclusive-interval main term `(N + 1) * H(N)`. -/
theorem smallAlong_error_le {g : ℕ → ℕ} (hg : ∀ n : ℕ, 0 < g n)
    (hmod : ∀ q : ℕ, 0 < q → ∀ n : ℕ, q ∣ g n ↔ q ∣ g (n % q)) (N : ℕ) :
    |smallAlong g N - ((N : ℝ) + 1) * rootReciprocalSum g N| ≤
      rootCountSummatory g N := by
  calc
    |smallAlong g N - ((N : ℝ) + 1) * rootReciprocalSum g N| =
        |∑ q ∈ Finset.Ioc 0 N,
          ((rootCountInRange g (N + 1) q : ℝ) -
            ((N : ℝ) + 1) * (rootCount g q : ℝ) / (q : ℝ))| := by
      rw [smallAlong_eq_sum_rootCountInRange hg, rootReciprocalSum,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      simp only [mul_div_assoc]
    _ ≤ ∑ q ∈ Finset.Ioc 0 N,
        |(rootCountInRange g (N + 1) q : ℝ) -
          ((N : ℝ) + 1) * (rootCount g q : ℝ) / (q : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ rootCountSummatory g N := by
      apply Finset.sum_le_sum
      intro q hq
      have hq0 := (Finset.mem_Ioc.mp hq).1
      simpa only [Nat.cast_add, Nat.cast_one] using
        rootCountInRange_error_le hq0 (hmod q hq0) (N + 1)

/-- A logarithmic root-reciprocal limit and an eventual linear root-count bound
imply the normalized small-divisor limit. No sign assumption on `C` or `κ`
is required. -/
theorem tendsto_smallAlong_of_root_bound {g : ℕ → ℕ} {κ C : ℝ}
    (hg : ∀ n : ℕ, 0 < g n)
    (hmod : ∀ q : ℕ, 0 < q → ∀ n : ℕ, q ∣ g n ↔ q ∣ g (n % q))
    (hH : Tendsto (fun N : ℕ ↦ rootReciprocalSum g N / Real.log (N : ℝ))
      atTop (𝓝 κ))
    (hP : ∀ᶠ N : ℕ in atTop, rootCountSummatory g N ≤ C * (N : ℝ)) :
    Tendsto (fun N : ℕ ↦ smallAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 κ) := by
  have hnat : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  have herror : Tendsto (fun N : ℕ ↦
      (smallAlong g N - ((N : ℝ) + 1) * rootReciprocalSum g N) /
        ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) ?_
      (hlog.const_div_atTop C)
    filter_upwards [hP, eventually_ge_atTop 2] with N hPN hN
    have hN1 : (1 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 1 < N by omega)
    have hN0 : (0 : ℝ) < (N : ℝ) := zero_lt_one.trans hN1
    have hden : (0 : ℝ) < (N : ℝ) * Real.log (N : ℝ) :=
      mul_pos hN0 (Real.log_pos hN1)
    simp only [abs_div, abs_of_pos hden]
    calc
      |smallAlong g N - ((N : ℝ) + 1) * rootReciprocalSum g N| /
          ((N : ℝ) * Real.log (N : ℝ)) ≤
          (C * (N : ℝ)) / ((N : ℝ) * Real.log (N : ℝ)) :=
        div_le_div_of_nonneg_right ((smallAlong_error_le hg hmod N).trans hPN) hden.le
      _ = C / Real.log (N : ℝ) := by
        rw [mul_comm C]
        exact mul_div_mul_left C (Real.log (N : ℝ)) (ne_of_gt hN0)
  have hfactor : Tendsto (fun N : ℕ ↦ ((N : ℝ) + 1) / (N : ℝ))
      atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).add
      (hnat.const_div_atTop 1)
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNz : (N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (show 0 < N by omega))
    rw [add_div, div_self hNz]
  have hmain := hfactor.mul hH
  simp only [one_mul] at hmain
  have ht := herror.add hmain
  simp only [zero_add] at ht
  apply ht.congr
  intro N
  rw [div_mul_div_comm, ← add_div]
  congr 1
  ring

/-- In particular, a finite real limit of `P(N) / N` is sufficient, in addition
to `H(N) / log N → κ`, to obtain `smallAlong g N / (N * log N) → κ`. -/
theorem tendsto_smallAlong_of_root_limits {g : ℕ → ℕ} {κ μ : ℝ}
    (hg : ∀ n : ℕ, 0 < g n)
    (hmod : ∀ q : ℕ, 0 < q → ∀ n : ℕ, q ∣ g n ↔ q ∣ g (n % q))
    (hH : Tendsto (fun N : ℕ ↦ rootReciprocalSum g N / Real.log (N : ℝ))
      atTop (𝓝 κ))
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory g N / (N : ℝ))
      atTop (𝓝 μ)) :
    Tendsto (fun N : ℕ ↦ smallAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 κ) := by
  apply tendsto_smallAlong_of_root_bound (C := μ + 1) hg hmod hH
  have hbound : ∀ᶠ N : ℕ in atTop,
      rootCountSummatory g N / (N : ℝ) ≤ μ + 1 :=
    hP.eventually_le_const (by linarith)
  filter_upwards [hbound, eventually_ge_atTop 1] with N hb hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  exact (div_le_iff₀ hN0).mp hb

end Erdos975Support
