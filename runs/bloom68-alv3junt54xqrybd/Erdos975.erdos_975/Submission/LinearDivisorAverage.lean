import Submission.RootMeanLinear
import Submission.QuadraticReduction

/-!
# The unconditional degree-one case of the polynomial divisor average

For a residue-invariant natural sequence which is eventually positive, the
small-divisor average has the same limit as its linear root-count mean. The
finitely many zero inputs contribute at most `O(N)` to the residue-counting
identity, despite the convention that zero has no natural divisors.

A linear upper bound on the values makes the divisors above the cutoff contribute
only `O(N)` as well. Applying these facts to the unconditional degree-one
root-count theorem proves the original floored divisor-average conclusion for
all irreducible degree-one integer polynomials which are eventually positive.
No root-count asymptotic is assumed in that conclusion, and no specification or
original conjecture is imported. No higher-degree conclusion is claimed.
-/

namespace Erdos975Support

open Filter Polynomial
open scoped Topology

/-- The number of zero values in the inclusive input interval. -/
def zeroInputCount (g : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((Finset.Iic N).filter fun n ↦ g n = 0).card

/-- The small-divisor/residue identity for an arbitrary sequence. Each zero
input is a divisibility root for all `N` positive moduli, but has no divisors. -/
theorem smallAlong_add_zeroInputCount_eq_sum_rootCountInRange
    (g : ℕ → ℕ) (N : ℕ) :
    smallAlong g N + (N : ℝ) * (zeroInputCount g N : ℝ) =
      ∑ q ∈ Finset.Ioc 0 N, (rootCountInRange g (N + 1) q : ℝ) := by
  have hIic : Finset.Iic N = Finset.range (N + 1) := by
    ext n
    simp only [Finset.mem_Iic, Finset.mem_range]
    omega
  have hpoint (n : ℕ) :
      (smallDivisorCount (g n) N : ℝ) +
          (N : ℝ) * (if g n = 0 then 1 else 0) =
        ∑ q ∈ Finset.Ioc 0 N, if q ∣ g n then (1 : ℝ) else 0 := by
    by_cases hn : g n = 0
    · simp [hn, smallDivisorCount]
    · rw [smallDivisorCount_eq_root_filter (Nat.pos_of_ne_zero hn),
        Finset.sum_boole]
      simp [hn]
  calc
    smallAlong g N + (N : ℝ) * (zeroInputCount g N : ℝ) =
        ∑ n ∈ Finset.Iic N,
          ((smallDivisorCount (g n) N : ℝ) +
            (N : ℝ) * (if g n = 0 then 1 else 0)) := by
      simp only [smallAlong, zeroInputCount, ← Finset.sum_boole,
        Finset.sum_add_distrib, Finset.mul_sum]
    _ = ∑ n ∈ Finset.Iic N, ∑ q ∈ Finset.Ioc 0 N,
        if q ∣ g n then (1 : ℝ) else 0 :=
      Finset.sum_congr rfl fun n _ ↦ hpoint n
    _ = ∑ q ∈ Finset.Ioc 0 N, ∑ n ∈ Finset.range (N + 1),
        if q ∣ g n then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm, hIic]
    _ = _ := by simp only [Finset.sum_boole, rootCountInRange]

/-- Positivity beyond `M` bounds the number of zero inputs by `M`, uniformly
in the cutoff. -/
lemma zeroInputCount_le_of_pos_tail {g : ℕ → ℕ} {M : ℕ}
    (hg : ∀ n : ℕ, M ≤ n → 0 < g n) (N : ℕ) :
    zeroInputCount g N ≤ M := by
  calc
    zeroInputCount g N ≤ (Finset.range M).card := by
      apply Finset.card_le_card
      intro n hn
      have hn0 := (Finset.mem_filter.mp hn).2
      apply Finset.mem_range.mpr
      by_contra h
      have := hg n (Nat.le_of_not_gt h)
      omega
    _ = M := Finset.card_range M

/-- Periodic counting still approximates the small-divisor sum when zeros
are present; their full contribution is displayed explicitly. -/
theorem smallAlong_error_le_with_zero_inputs {g : ℕ → ℕ}
    (hmod : ∀ q : ℕ, 0 < q → ∀ n : ℕ, q ∣ g n ↔ q ∣ g (n % q)) (N : ℕ) :
    |smallAlong g N - ((N : ℝ) + 1) * rootReciprocalSum g N| ≤
      rootCountSummatory g N + (N : ℝ) * (zeroInputCount g N : ℝ) := by
  have hroot :
      |smallAlong g N + (N : ℝ) * (zeroInputCount g N : ℝ) -
          ((N : ℝ) + 1) * rootReciprocalSum g N| ≤
        rootCountSummatory g N := by
    calc
      _ = |∑ q ∈ Finset.Ioc 0 N,
          ((rootCountInRange g (N + 1) q : ℝ) -
            ((N : ℝ) + 1) * (rootCount g q : ℝ) / (q : ℝ))| := by
        rw [smallAlong_add_zeroInputCount_eq_sum_rootCountInRange,
          rootReciprocalSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
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
  calc
    _ = |(smallAlong g N + (N : ℝ) * (zeroInputCount g N : ℝ) -
        ((N : ℝ) + 1) * rootReciprocalSum g N) -
          (N : ℝ) * (zeroInputCount g N : ℝ)| := by
      congr 1
      ring
    _ ≤ |smallAlong g N + (N : ℝ) * (zeroInputCount g N : ℝ) -
        ((N : ℝ) + 1) * rootReciprocalSum g N| +
          |(N : ℝ) * (zeroInputCount g N : ℝ)| := abs_sub _ _
    _ ≤ rootCountSummatory g N + (N : ℝ) * (zeroInputCount g N : ℝ) := by
      simpa only [abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ (N : ℝ) * (zeroInputCount g N : ℝ))] using
          add_le_add_left hroot |(N : ℝ) * (zeroInputCount g N : ℝ)|

/-- Eventual positivity suffices for the small-divisor mean. In particular,
one does not have to exclude an integer root of a degree-one polynomial. -/
theorem tendsto_smallAlong_of_eventual_pos_linear_rootCount {g : ℕ → ℕ} {κ : ℝ}
    (hg : ∀ᶠ n : ℕ in atTop, 0 < g n)
    (hmod : ∀ q : ℕ, 0 < q → ∀ n : ℕ, q ∣ g n ↔ q ∣ g (n % q))
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory g N / (N : ℝ))
      atTop (𝓝 κ)) :
    Tendsto (fun N : ℕ ↦ smallAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 κ) := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp hg
  obtain ⟨B, _, hB⟩ := rootCountSummatory_le_const_mul_of_tendsto hP
  have herror : Tendsto (fun N : ℕ ↦
      (smallAlong g N - ((N : ℝ) + 1) * rootReciprocalSum g N) /
        ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    have ht := tendsto_div_mul_log_of_eventual_linear_bound
      (u := fun N ↦ |smallAlong g N - ((N : ℝ) + 1) * rootReciprocalSum g N|)
      (A := B + (M : ℝ)) (fun N ↦ abs_nonneg _) (Eventually.of_forall fun N ↦ by
        calc
          _ ≤ rootCountSummatory g N + (N : ℝ) * (zeroInputCount g N : ℝ) :=
            smallAlong_error_le_with_zero_inputs hmod N
          _ ≤ B * (N : ℝ) + (N : ℝ) * (M : ℝ) := by
            apply add_le_add (hB N)
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
            exact_mod_cast zeroInputCount_le_of_pos_tail hM N
          _ = (B + (M : ℝ)) * (N : ℝ) := by ring)
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN1 : (1 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 1 < N by omega)
    simp only [Function.comp_apply, abs_div, abs_of_pos (mul_pos (zero_lt_one.trans hN1)
      (Real.log_pos hN1))]
  have hfactor : Tendsto (fun N : ℕ ↦ ((N : ℝ) + 1) / (N : ℝ))
      atTop (𝓝 1) := by
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).add
      ((tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop).const_div_atTop 1)
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNz : (N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (show 0 < N by omega))
    rw [add_div, div_self hNz]
  have hmain := hfactor.mul (tendsto_rootReciprocalSum_of_rootCountSummatory hP)
  simp only [one_mul] at hmain
  have ht := herror.add hmain
  simp only [zero_add] at ht
  apply ht.congr
  intro N
  rw [div_mul_div_comm, ← add_div]
  congr 1
  ring

/-- Partition all natural divisors at the cutoff. This includes `m = 0`. -/
lemma sigma_zero_eq_small_add_large (m N : ℕ) :
    ArithmeticFunction.sigma0 m = smallDivisorCount m N +
      (m.divisors.filter fun q ↦ N < q).card := by
  rw [ArithmeticFunction.sigma_zero_apply]
  simpa only [smallDivisorCount, not_le] using
    (Finset.card_filter_add_card_filter_not (s := m.divisors) (fun q ↦ q ≤ N)).symm

/-- The difference between the full sum and the small-divisor sum counts
precisely the divisors above the cutoff. -/
lemma divisorAlong_sub_smallAlong_eq_sum_large (g : ℕ → ℕ) (N : ℕ) :
    divisorAlong g N - smallAlong g N =
      ∑ n ∈ Finset.Iic N, (((g n).divisors.filter fun q ↦ N < q).card : ℝ) := by
  unfold divisorAlong smallAlong
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [sigma_zero_eq_small_add_large]
  push_cast
  ring

lemma divisorAlong_sub_smallAlong_nonneg (g : ℕ → ℕ) (N : ℕ) :
    0 ≤ divisorAlong g N - smallAlong g N := by
  rw [divisorAlong_sub_smallAlong_eq_sum_large]
  exact Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _

/-- A divisor above `N` of a linearly bounded value at input `n ≤ N` lies
in `N < q ≤ 2 K N`. -/
lemma largeDivisor_mem_Ioc_of_linear_upper {g : ℕ → ℕ} {K N n q : ℕ}
    (hupper : ∀ n : ℕ, g n ≤ K * (n + 1)) (hN : 1 ≤ N) (hn : n ≤ N)
    (hq : q ∈ (g n).divisors.filter (fun q ↦ N < q)) :
    q ∈ Finset.Ioc N (2 * K * N) := by
  obtain ⟨hqd, hqN⟩ := Finset.mem_filter.mp hq
  refine Finset.mem_Ioc.mpr ⟨hqN, ?_⟩
  calc
    q ≤ g n := Nat.divisor_le hqd
    _ ≤ K * (n + 1) := hupper n
    _ ≤ K * (2 * N) := Nat.mul_le_mul_left K (by omega)
    _ = 2 * K * N := by ring

/-- Each modulus `q > N` sees the input interval inside a single residue
range. Hence the entire large-divisor contribution is bounded by `P(2 K N)`.
Neither positivity nor residue invariance is needed for this bound. -/
theorem divisorAlong_sub_smallAlong_le_rootCountSummatory_of_linear_upper
    {g : ℕ → ℕ} {K : ℕ} (hupper : ∀ n : ℕ, g n ≤ K * (n + 1))
    (N : ℕ) (hN : 1 ≤ N) :
    divisorAlong g N - smallAlong g N ≤ rootCountSummatory g (2 * K * N) := by
  have hIic : Finset.Iic N = Finset.range (N + 1) := by
    ext n
    simp only [Finset.mem_Iic, Finset.mem_range]
    omega
  have hpoint (n : ℕ) (hn : n ∈ Finset.Iic N) :
      ((g n).divisors.filter (fun q ↦ N < q)).card ≤
        ((Finset.Ioc N (2 * K * N)).filter (fun q ↦ q ∣ g n)).card := by
    apply Finset.card_le_card
    intro q hq
    exact Finset.mem_filter.mpr
      ⟨largeDivisor_mem_Ioc_of_linear_upper hupper hN (Finset.mem_Iic.mp hn) hq,
        Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hq).1⟩
  calc
    divisorAlong g N - smallAlong g N ≤ ∑ n ∈ Finset.Iic N,
        (((Finset.Ioc N (2 * K * N)).filter (fun q ↦ q ∣ g n)).card : ℝ) := by
      rw [divisorAlong_sub_smallAlong_eq_sum_large]
      exact Finset.sum_le_sum fun n hn ↦ by exact_mod_cast hpoint n hn
    _ = ∑ q ∈ Finset.Ioc N (2 * K * N),
        (rootCountInRange g (N + 1) q : ℝ) := by
      simp only [← Finset.sum_boole]
      rw [Finset.sum_comm, hIic]
      simp only [rootCountInRange, Finset.sum_boole]
    _ ≤ ∑ q ∈ Finset.Ioc N (2 * K * N), (rootCount g q : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hNq : N + 1 ≤ q := by
        have := (Finset.mem_Ioc.mp hq).1
        omega
      exact_mod_cast (show rootCountInRange g (N + 1) q ≤ rootCount g q from
        Finset.card_le_card
          (Finset.filter_subset_filter _ (Finset.range_mono hNq)))
    _ ≤ rootCountSummatory g (2 * K * N) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro q hq
        obtain ⟨hqN, hqK⟩ := Finset.mem_Ioc.mp hq
        exact Finset.mem_Ioc.mpr ⟨by omega, hqK⟩
      · intro q _ _
        exact Nat.cast_nonneg _

/-- A finite root-count mean makes the large-divisor error negligible for
any linearly bounded natural sequence. -/
theorem tendsto_divisorAlong_sub_smallAlong_of_linear_upper
    {g : ℕ → ℕ} {κ : ℝ}
    (hupper : ∃ K : ℕ, ∀ n : ℕ, g n ≤ K * (n + 1))
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory g N / (N : ℝ))
      atTop (𝓝 κ)) :
    Tendsto (fun N : ℕ ↦ (divisorAlong g N - smallAlong g N) /
      ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := hupper
  obtain ⟨B, _, hB⟩ := rootCountSummatory_le_const_mul_of_tendsto hP
  apply tendsto_div_mul_log_of_eventual_linear_bound
    (A := B * (2 * (K : ℝ))) (divisorAlong_sub_smallAlong_nonneg g)
  filter_upwards [eventually_ge_atTop 1] with N hN
  calc
    divisorAlong g N - smallAlong g N ≤ rootCountSummatory g (2 * K * N) :=
      divisorAlong_sub_smallAlong_le_rootCountSummatory_of_linear_upper hK N hN
    _ ≤ B * ((2 * K * N : ℕ) : ℝ) := hB _
    _ = (B * (2 * (K : ℝ))) * (N : ℝ) := by push_cast; ring

/-- Eventual positivity, residue invariance, linear growth and a root-count
mean determine the full divisor average, with the same constant. -/
theorem tendsto_divisorAlong_of_linear_growth
    {g : ℕ → ℕ} {κ : ℝ}
    (hg : ∀ᶠ n : ℕ in atTop, 0 < g n)
    (hmod : ∀ q : ℕ, 0 < q → ∀ n : ℕ, q ∣ g n ↔ q ∣ g (n % q))
    (hupper : ∃ K : ℕ, ∀ n : ℕ, g n ≤ K * (n + 1))
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory g N / (N : ℝ))
      atTop (𝓝 κ)) :
    Tendsto (fun N : ℕ ↦ divisorAlong g N / ((N : ℝ) * Real.log (N : ℝ)))
      atTop (𝓝 κ) := by
  have ht := (tendsto_divisorAlong_sub_smallAlong_of_linear_upper hupper hP).add
    (tendsto_smallAlong_of_eventual_pos_linear_rootCount hg hmod hP)
  simp only [zero_add] at ht
  apply ht.congr
  intro N
  rw [← add_div]
  congr 1
  ring

/-- Every affine integer polynomial has a uniform natural linear upper bound
on its absolute values, including negative leading coefficients. -/
theorem polynomialAbsValue_linear_upper_bound (f : ℤ[X]) (hdeg : f.natDegree = 1) :
    ∃ K : ℕ, ∀ n : ℕ, polynomialAbsValue f n ≤ K * (n + 1) := by
  obtain ⟨a, ha, b, rfl⟩ := natDegree_eq_one.mp hdeg
  refine ⟨a.natAbs + b.natAbs, fun n ↦ ?_⟩
  simp only [polynomialAbsValue, eval_add, eval_mul, eval_C, eval_X]
  calc
    (a * (n : ℤ) + b).natAbs ≤ (a * (n : ℤ)).natAbs + b.natAbs :=
      Int.natAbs_add_le _ _
    _ = a.natAbs * n + b.natAbs := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]
    _ ≤ (a.natAbs + b.natAbs) * (n + 1) := by
      nlinarith [Nat.zero_le a.natAbs, Nat.zero_le (b.natAbs * n)]

/-- A degree-one polynomial has no zero value beyond the absolute value of
its constant coefficient. No sign or irreducibility assumption is needed. -/
theorem eventual_polynomialAbsValue_pos_of_natDegree_eq_one
    (f : ℤ[X]) (hdeg : f.natDegree = 1) :
    ∀ᶠ n : ℕ in atTop, 0 < polynomialAbsValue f n := by
  obtain ⟨a, ha, b, rfl⟩ := natDegree_eq_one.mp hdeg
  filter_upwards [eventually_gt_atTop b.natAbs] with n hn
  apply Int.natAbs_pos.mpr
  simp only [eval_add, eval_mul, eval_C, eval_X]
  intro he
  have hab : a * (n : ℤ) = -b := by linear_combination he
  have habs := congrArg Int.natAbs hab
  simp only [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_neg] at habs
  have hnle := Nat.le_mul_of_pos_left n (Int.natAbs_pos.mpr ha)
  omega

/-- In degree one the natural-cutoff divisor average equals the root-count
mean, without requiring positivity at every input. -/
theorem tendsto_polynomial_divisorAlong_of_linear_root_mean
    (f : ℤ[X]) (hdeg : f.natDegree = 1) {κ : ℝ}
    (hP : Tendsto (fun N : ℕ ↦ rootCountSummatory (polynomialAbsValue f) N / (N : ℝ))
      atTop (𝓝 κ)) :
    Tendsto (fun N : ℕ ↦ divisorAlong (polynomialAbsValue f) N /
      ((N : ℝ) * Real.log (N : ℝ))) atTop (𝓝 κ) := by
  exact tendsto_divisorAlong_of_linear_growth
    (eventual_polynomialAbsValue_pos_of_natDegree_eq_one f hdeg)
    (polynomialAbsValue_mod_dvd f) (polynomialAbsValue_linear_upper_bound f hdeg) hP

/-- The unconditional natural-cutoff degree-one theorem, with its explicit
constant. It applies to nonmonic polynomials and either sign of the leading
coefficient. -/
theorem tendsto_polynomial_divisorAlong_of_natDegree_eq_one
    (f : ℤ[X]) (hf : Irreducible f) (hdeg : f.natDegree = 1) :
    Tendsto (fun N : ℕ ↦ divisorAlong (polynomialAbsValue f) N /
      ((N : ℝ) * Real.log (N : ℝ))) atTop
        (𝓝 ((f.leadingCoeff.natAbs.totient : ℝ) / (f.leadingCoeff.natAbs : ℝ))) := by
  obtain ⟨a, ha, b, rfl⟩ := natDegree_eq_one.mp hdeg
  rw [leadingCoeff_linear ha]
  exact tendsto_polynomial_divisorAlong_of_linear_root_mean _ (natDegree_linear ha)
    (tendsto_rootCountSummatory_affine a b ha
      (affine_coefficients_isCoprime a b (hf.isPrimitive (by omega))))

/-- Transfer the unconditional degree-one theorem to real cutoffs and the
original floor convention under the original eventual positivity hypothesis. -/
theorem tendsto_flooredPolynomialSum_of_natDegree_eq_one
    (f : ℤ[X]) (hf : Irreducible f) (hdeg : f.natDegree = 1)
    (hpos : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    Tendsto (fun x : ℝ ↦ flooredPolynomialSum f x / (x * Real.log x)) atTop
      (𝓝 ((f.leadingCoeff.natAbs.totient : ℝ) / (f.leadingCoeff.natAbs : ℝ))) :=
  (flooredPolynomialSum_limit_iff f hpos _).mpr
    (tendsto_polynomial_divisorAlong_of_natDegree_eq_one f hf hdeg)

/-- The complete known degree-one case of the actual divisor-average
conclusion: only degree one, irreducibility and eventual positivity are
hypotheses. In particular, no root-count mean is assumed. -/
theorem linear_divisor_average (f : ℤ[X]) (hdeg : f.natDegree = 1)
    (hf : Irreducible f) (hpos : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    ∃ c > (0 : ℝ), Tendsto (fun x : ℝ ↦
      flooredPolynomialSum f x / (x * Real.log x)) atTop (𝓝 c) := by
  obtain ⟨κ, hκ, hP⟩ := exists_pos_rootMean_of_natDegree_eq_one f hf hdeg
  exact ⟨κ, hκ, (flooredPolynomialSum_limit_iff f hpos κ).mpr
    (tendsto_polynomial_divisorAlong_of_linear_root_mean f hdeg hP)⟩

/-- The same degree-one conclusion with the sum fully expanded, matching
the original inclusive sum and its floor-of-integer-value convention, without
importing `Submission.Spec`. This is not a theorem for arbitrary degrees. -/
theorem erdos_975_of_natDegree_eq_one :
    ∀ f : ℤ[X], f.natDegree = 1 → Irreducible f →
      (∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) →
      ∃ c > (0 : ℝ), Tendsto (fun x : ℝ ↦
        (∑ n ∈ Finset.Iic (Nat.floor x),
          (ArithmeticFunction.sigma0 (Nat.floor (f.eval (n : ℤ))) : ℝ)) /
            (x * Real.log x)) atTop (𝓝 c) := by
  intro f hdeg hf hpos
  exact linear_divisor_average f hdeg hf hpos

end Erdos975Support
