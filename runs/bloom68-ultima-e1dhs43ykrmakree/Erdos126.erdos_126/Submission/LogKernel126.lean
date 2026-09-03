import FormalConjecturesUtil

/-!
# Logarithmic kernels for Erdős problem 126

The log-sum kernel on positive reals is conditionally negative semidefinite.
The log-gcd kernel and equality-of-valuations kernel are positive semidefinite.
All statements allow repeated inputs and arbitrary real coefficients.

The analytic proof uses the Möbius transform `(a - 1) / (a + 1)` and the power
series for `-log (1 - x)`. The arithmetic proof uses the nonnegative von Mangoldt
divisor expansion of the logarithm.
-/

namespace E126

open scoped BigOperators

namespace LogKernel

/-- The quadratic form of a rank-one kernel is a square. -/
lemma rank_one_sum {ι : Type*} [Fintype ι] (q v : ι → ℝ) :
    (∑ i, ∑ j, q i * q j * (v i * v j)) = (∑ i, q i * v i) ^ 2 := by
  classical
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Terms depending on only one of the two indices vanish on zero-sum vectors. -/
lemma separated_sum_eq_zero {ι : Type*} [Fintype ι] (q u v : ι → ℝ) (c : ℝ)
    (hq : ∑ i, q i = 0) :
    (∑ i, ∑ j, q i * q j * (u i + v j + c)) = 0 := by
  classical
  have hu : (∑ i, ∑ j, q i * q j * u i) = 0 := by
    calc
      _ = (∑ i, q i * u i) * (∑ j, q j) := by
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hq, mul_zero]
  have hv : (∑ i, ∑ j, q i * q j * v j) = 0 := by
    calc
      _ = (∑ i, q i) * (∑ j, q j * v j) := by
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hq, zero_mul]
  have hc : (∑ i, ∑ j, q i * q j * c) = 0 := by
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum, hq, mul_zero, Finset.sum_const_zero,
      zero_mul]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hu, hv, hc]
  ring

lemma abs_mobius_lt_one {a : ℝ} (ha : 0 < a) :
    |(a - 1) / (a + 1)| < 1 := by
  have hp : 0 < a + 1 := by linarith
  rw [abs_lt]
  constructor
  · rw [lt_div_iff₀ hp]
    linarith
  · rw [div_lt_iff₀ hp]
    linarith

lemma abs_mul_lt_one {x y : ℝ} (hx : |x| < 1) (hy : |y| < 1) :
    |x * y| < 1 := by
  calc
    |x * y| = |x| * |y| := abs_mul x y
    _ ≤ 1 * |y| := mul_le_mul_of_nonneg_right hx.le (abs_nonneg y)
    _ < 1 := by simpa using hy

/-- The log-sum kernel differs from a power-series kernel by separated terms. -/
lemma log_add_mobius {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a + b) = Real.log (a + 1) + Real.log (b + 1) - Real.log 2 +
      Real.log (1 - ((a - 1) / (a + 1)) * ((b - 1) / (b + 1))) := by
  have ha1 : a + 1 ≠ 0 := by positivity
  have hb1 : b + 1 ≠ 0 := by positivity
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have heq : 1 - ((a - 1) / (a + 1)) * ((b - 1) / (b + 1)) =
      (2 * (a + b)) / ((a + 1) * (b + 1)) := by
    field_simp
    ring
  rw [heq, Real.log_div (mul_ne_zero (by norm_num) hab) (mul_ne_zero ha1 hb1),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hab, Real.log_mul ha1 hb1]
  ring

/-- The kernel `-log (1 - rᵢ rⱼ)` is positive semidefinite for `|rᵢ| < 1`. -/
lemma neg_log_one_sub_mul_psd {ι : Type*} [Fintype ι] (r q : ι → ℝ)
    (hr : ∀ i, |r i| < 1) :
    0 ≤ ∑ i, ∑ j, q i * q j * (-Real.log (1 - r i * r j)) := by
  classical
  have hs : HasSum
      (fun n : ℕ => ∑ i, ∑ j,
        q i * q j * ((r i * r j) ^ (n + 1) / ((n : ℝ) + 1)))
      (∑ i, ∑ j, q i * q j * (-Real.log (1 - r i * r j))) := by
    apply hasSum_sum
    intro i hi
    apply hasSum_sum
    intro j hj
    exact (Real.hasSum_pow_div_log_of_abs_lt_one
      (abs_mul_lt_one (hr i) (hr j))).mul_left (q i * q j)
  apply HasSum.nonneg _ hs
  intro n
  have heq : (∑ i, ∑ j,
      q i * q j * ((r i * r j) ^ (n + 1) / ((n : ℝ) + 1))) =
      (∑ i, q i * r i ^ (n + 1)) ^ 2 / ((n : ℝ) + 1) := by
    rw [← rank_one_sum q (fun i => r i ^ (n + 1))]
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_pow]
    ring
  rw [heq]
  positivity

end LogKernel

/-- Weak conditional negative definiteness of the log-sum kernel on positive reals.
No injectivity or distinctness hypothesis is required. -/
theorem log_sum_cnd {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (q : ι → ℝ) (hq : ∑ i, q i = 0) :
    (∑ i, ∑ j, q i * q j * Real.log (a i + a j)) ≤ 0 := by
  classical
  let r : ι → ℝ := fun i => (a i - 1) / (a i + 1)
  have hr : ∀ i, |r i| < 1 := fun i => LogKernel.abs_mobius_lt_one (ha i)
  have hn := LogKernel.neg_log_one_sub_mul_psd r q hr
  have hz := LogKernel.separated_sum_eq_zero q
    (fun i => Real.log (a i + 1)) (fun i => Real.log (a i + 1)) (-Real.log 2) hq
  have heq : (∑ i, ∑ j, q i * q j * Real.log (a i + a j)) =
      ∑ i, ∑ j, q i * q j * Real.log (1 - r i * r j) := by
    calc
      _ = (∑ i, ∑ j, q i * q j *
          (Real.log (a i + 1) + Real.log (a j + 1) + -Real.log 2)) +
          ∑ i, ∑ j, q i * q j * Real.log (1 - r i * r j) := by
        simp_rw [LogKernel.log_add_mobius (ha _) (ha _), sub_eq_add_neg,
          mul_add, Finset.sum_add_distrib]
        rfl
      _ = _ := by rw [hz, zero_add]
  rw [heq]
  simpa only [mul_neg, Finset.sum_neg_distrib, neg_nonneg] using hn

/-- The natural-number specialization of `log_sum_cnd`. -/
theorem log_sum_nat_cnd {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (ha : ∀ i, 0 < a i) (q : ι → ℝ) (hq : ∑ i, q i = 0) :
    (∑ i, ∑ j, q i * q j * Real.log ((a i + a j : ℕ) : ℝ)) ≤ 0 := by
  simpa only [Nat.cast_add] using
    log_sum_cnd (fun i => (a i : ℝ)) (fun i => Nat.cast_pos.mpr (ha i)) q hq

namespace LogKernel

/-- A finite weighted feature kernel is a sum of squares. -/
lemma weighted_feature_sum {ι κ : Type*} [Fintype ι]
    (s : Finset κ) (w : κ → ℝ) (v : κ → ι → ℝ) (q : ι → ℝ) :
    (∑ i, ∑ j, q i * q j * (∑ k ∈ s, w k * (v k i * v k j))) =
      ∑ k ∈ s, w k * (∑ i, q i * v k i) ^ 2 := by
  classical
  simp_rw [Finset.mul_sum]
  calc
    (∑ i, ∑ j, ∑ k ∈ s, q i * q j * (w k * (v k i * v k j))) =
        ∑ i, ∑ k ∈ s, ∑ j, q i * q j * (w k * (v k i * v k j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ k ∈ s, ∑ i, ∑ j, q i * q j * (w k * (v k i * v k j)) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← rank_one_sum q (v k), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

lemma weighted_feature_psd {ι κ : Type*} [Fintype ι]
    (s : Finset κ) (w : κ → ℝ) (v : κ → ι → ℝ) (q : ι → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) :
    0 ≤ ∑ i, ∑ j, q i * q j * (∑ k ∈ s, w k * (v k i * v k j)) := by
  rw [weighted_feature_sum]
  exact Finset.sum_nonneg (fun k hk => mul_nonneg (hw k hk) (sq_nonneg _))

/-- Equality of labels is a sum of indicator rank-one kernels. -/
lemma equality_eq_features {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (v : ι → κ) (i j : ι) :
    (if v i = v j then (1 : ℝ) else 0) =
      ∑ k ∈ Finset.univ.image v,
        (if v i = k then (1 : ℝ) else 0) * (if v j = k then (1 : ℝ) else 0) := by
  classical
  have hi : v i ∈ Finset.univ.image v := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, hi, if_true]
  simp only [eq_comm]

/-- Expand log-gcd into nonnegative divisor features using von Mangoldt's identity. -/
lemma log_gcd_eq_features {a b M : ℕ} (hg : Nat.gcd a b ≠ 0) (hM : M ≠ 0)
    (hdiv : Nat.gcd a b ∣ M) :
    Real.log (Nat.gcd a b : ℝ) =
      ∑ d ∈ M.divisors, ArithmeticFunction.vonMangoldt d *
        ((if d ∣ a then (1 : ℝ) else 0) * (if d ∣ b then (1 : ℝ) else 0)) := by
  rw [← ArithmeticFunction.vonMangoldt_sum]
  apply Finset.sum_subset_zero_on_sdiff (Nat.divisors_subset_of_dvd hM hdiv)
  · intro d hd
    have hnot : ¬d ∣ Nat.gcd a b := by
      intro hdg
      exact (Finset.mem_sdiff.mp hd).2 (Nat.mem_divisors.mpr ⟨hdg, hg⟩)
    by_cases hda : d ∣ a
    · have hdb : ¬d ∣ b := fun hdb => hnot (Nat.dvd_gcd hda hdb)
      simp [hdb]
    · simp [hda]
  · intro d hd
    obtain ⟨hda, hdb⟩ := Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors hd)
    simp [hda, hdb]

end LogKernel

/-- The equivalence-class matrix of any labeling is positive semidefinite.
The label type need not itself be finite. -/
theorem equivalence_class_psd {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (v : ι → κ) (q : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, q i * q j * (if v i = v j then (1 : ℝ) else 0) := by
  classical
  have h := LogKernel.weighted_feature_psd (Finset.univ.image v) (fun _ => (1 : ℝ))
    (fun k i => if v i = k then (1 : ℝ) else 0) q (by intros; norm_num)
  simpa only [one_mul, ← LogKernel.equality_eq_features v] using h

/-- A nonnegative multiple of an equivalence-class matrix is positive semidefinite. -/
theorem equivalence_class_weighted_psd {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (v : ι → κ) (q : ι → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    0 ≤ ∑ i, ∑ j, q i * q j * (if v i = v j then c else 0) := by
  have heq : (∑ i, ∑ j, q i * q j * (if v i = v j then c else 0)) =
      (∑ i, ∑ j, q i * q j * (if v i = v j then (1 : ℝ) else 0)) * c := by
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  rw [heq]
  exact mul_nonneg (equivalence_class_psd v q) hc

/-- Equality of the exponents of `2` in the natural-number factorizations is PSD. -/
theorem factorization_two_psd {ι : Type*} [Fintype ι] (a : ι → ℕ) (q : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, q i * q j *
      (if (a i).factorization 2 = (a j).factorization 2 then (1 : ℝ) else 0) :=
  equivalence_class_psd (fun i => (a i).factorization 2) q

/-- The same equality-of-valuations PSD statement using `padicValNat`. -/
theorem padicValNat_two_psd {ι : Type*} [Fintype ι] (a : ι → ℕ) (q : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, q i * q j *
      (if padicValNat 2 (a i) = padicValNat 2 (a j) then (1 : ℝ) else 0) :=
  equivalence_class_psd (fun i => padicValNat 2 (a i)) q

/-- Positive semidefiniteness of log-gcd on positive natural numbers. -/
theorem log_gcd_psd {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (ha : ∀ i, 0 < a i) (q : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, q i * q j * Real.log (Nat.gcd (a i) (a j) : ℝ) := by
  classical
  let M : ℕ := ∏ i, a i
  have hM : M ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (ha i).ne')
  have hlog : ∀ i j, Real.log (Nat.gcd (a i) (a j) : ℝ) =
      ∑ d ∈ M.divisors, ArithmeticFunction.vonMangoldt d *
        ((if d ∣ a i then (1 : ℝ) else 0) * (if d ∣ a j then (1 : ℝ) else 0)) := by
    intro i j
    apply LogKernel.log_gcd_eq_features (Nat.gcd_ne_zero_left (ha i).ne') hM
    exact (Nat.gcd_dvd_left (a i) (a j)).trans (Finset.dvd_prod_of_mem a (Finset.mem_univ i))
  simp_rw [hlog]
  exact LogKernel.weighted_feature_psd M.divisors ArithmeticFunction.vonMangoldt
    (fun d i => if d ∣ a i then (1 : ℝ) else 0) q
    (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)

/-- The arithmetic logarithmic kernel used for Erdős problem 126. -/
noncomputable def arithmetic_log_kernel (a b : ℕ) : ℝ :=
  Real.log ((a + b : ℕ) : ℝ) - Real.log (Nat.gcd a b : ℝ) -
    (if a.factorization 2 = b.factorization 2 then Real.log 2 else 0)

/-- The arithmetic logarithmic kernel is weakly conditionally negative semidefinite. -/
theorem arithmetic_log_kernel_cnd {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (ha : ∀ i, 0 < a i) (q : ι → ℝ) (hq : ∑ i, q i = 0) :
    (∑ i, ∑ j, q i * q j * arithmetic_log_kernel (a i) (a j)) ≤ 0 := by
  have hs := log_sum_nat_cnd a ha q hq
  have hg := log_gcd_psd a ha q
  have hv := equivalence_class_weighted_psd (fun i => (a i).factorization 2) q
    (Real.log 2) (Real.log_nonneg (by norm_num))
  simp only [arithmetic_log_kernel, mul_sub, Finset.sum_sub_distrib]
  linarith

/-- On positive inputs the arithmetic logarithmic kernel has zero diagonal. -/
@[simp] theorem arithmetic_log_kernel_diag {a : ℕ} (ha : 0 < a) :
    arithmetic_log_kernel a a = 0 := by
  have haR : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  rw [arithmetic_log_kernel, Nat.gcd_self, if_pos rfl, Nat.cast_add, ← two_mul,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) haR]
  ring

end E126
