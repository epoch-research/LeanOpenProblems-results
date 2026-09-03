import Submission.ExponentialSum
import Submission.Vaughan
import Submission.DivisorEnergy

/-! Finite exponential sums of the algebraic Vaughan decomposition.
These are single-variable prime estimates, not prime-pair correlation estimates. -/
namespace Erdos972VaughanSums
open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972ExponentialSum Erdos972Vaughan Erdos972DivisorEnergy

noncomputable def expSum (f : ArithmeticFunction ℝ) (θ : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Ioc 0 N, (f n : ℂ) * phase (θ * n)

lemma expSum_convolution (f g : ArithmeticFunction ℝ) (θ : ℝ) (N : ℕ) :
    expSum (f * g) θ N =
      ∑ m ∈ Ioc 0 N, (f m : ℂ) *
        ∑ n ∈ Ioc 0 (N / m), (g n : ℂ) * phase (θ * m * n) := by
  have he (n : ℕ) : ((f * g) n : ℂ) * phase (θ * n) =
      ∑ ab ∈ n.divisorsAntidiagonal,
        (f ab.1 : ℂ) * (g ab.2 : ℂ) * phase (θ * ab.1 * ab.2) := by
    rw [ArithmeticFunction.mul_apply, Complex.ofReal_sum, sum_mul]
    apply sum_congr rfl
    intro ab hab
    rw [Complex.ofReal_mul, ← (Nat.mem_divisorsAntidiagonal.mp hab).1, Nat.cast_mul,
      ← mul_assoc θ]
  unfold expSum
  simp_rw [he]
  rw [sum_divisorsAntidiagonal_eq_sum_hyperbola
    (fun m n => (f m : ℂ) * (g n : ℂ) * phase (θ * m * n)) N]
  simp only [mul_sum, mul_assoc]

lemma expSum_convolution_support (f g : ArithmeticFunction ℝ) (R : ℕ)
    (hf : ∀ n, R < n → f n = 0) (θ : ℝ) (N : ℕ) :
    expSum (f * g) θ N =
      ∑ m ∈ Ioc 0 (min R N), (f m : ℂ) *
        ∑ n ∈ Ioc 0 (N / m), (g n : ℂ) * phase (θ * m * n) := by
  rw [expSum_convolution]
  symm
  apply sum_subset
  · intro m hm
    exact mem_Ioc.mpr ⟨(mem_Ioc.mp hm).1, (mem_Ioc.mp hm).2.trans (min_le_right _ _)⟩
  · intro m hm hnot
    have hRm : R < m := by
      have hmN := mem_Ioc.mp hm
      simp only [mem_Ioc, le_min_iff, hmN.1, hmN.2, and_true, true_and] at hnot
      omega
    simp [hf m hRm]

lemma expSum_convolution_zeta_support (f : ArithmeticFunction ℝ) (R : ℕ)
    (hf : ∀ n, R < n → f n = 0) (θ : ℝ) (N : ℕ) :
    expSum (f * ζ) θ N =
      ∑ m ∈ Ioc 0 (min R N), (f m : ℂ) *
        ∑ n ∈ Ioc 0 (N / m), phase (θ * m * n) := by
  rw [expSum_convolution_support f ζ R hf]
  apply sum_congr rfl
  intro m hm
  congr 1
  apply sum_congr rfl
  intro n hn
  simp only [natCoe_apply, zeta_apply_ne (Nat.ne_of_gt (mem_Ioc.mp hn).1),
    Nat.cast_one, Complex.ofReal_one, one_mul]

/-- The logarithmic Type-I term in the actual Vaughan decomposition. -/
theorem vaughan_first_typeI_bound {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (U N : ℕ) (hU : 8 * U ≤ q) :
    ‖expSum (cutoff (μ : ArithmeticFunction ℝ) U * ArithmeticFunction.log) θ N‖ ≤
      4 * Real.log (N + 1) * q * (2 + Real.log q) := by
  rw [expSum_convolution_support _ _ U
    (fun n hn => cutoff_eq_zero_of_lt _ hn)]
  have h := near_rational_typeI_positive_log_bound a haq θ hθ
    (Ioc 0 (min U N)) U (fun m hm =>
      ⟨(mem_Ioc.mp hm).1, (mem_Ioc.mp hm).2.trans (min_le_left _ _)⟩)
    hU (fun m => N / m) N (fun m hm => Nat.div_le_self N m)
    (fun m => (cutoff (μ : ArithmeticFunction ℝ) U m : ℂ)) 1 (by norm_num)
    (fun m hm => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_cutoff_moebius_le_one U m)
  simpa only [ArithmeticFunction.log_apply, mul_one] using h

/-- The second Type-I term is a zeta convolution with a coefficient supported
up to `U*V` and bounded by `log(U*V)`. -/
theorem vaughan_second_typeI_bound {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (U V N : ℕ) (hUV : 8 * (U * V) ≤ q) :
    ‖expSum (cutoff (μ : ArithmeticFunction ℝ) U * ζ * cutoff Λ V) θ N‖ ≤
      2 * Real.log (U * V) * q * (2 + Real.log q) := by
  have he : cutoff (μ : ArithmeticFunction ℝ) U * ζ * cutoff Λ V =
      (cutoff (μ : ArithmeticFunction ℝ) U * cutoff Λ V) * ζ := by ring
  rw [he, expSum_convolution_zeta_support _ (U * V)
    (fun n hn => cutoff_mul_cutoff_eq_zero_of_lt _ _ U V n hn)]
  apply near_rational_typeI_positive_bound a haq θ hθ
    (Ioc 0 (min (U * V) N)) (U * V) (fun m hm =>
      ⟨(mem_Ioc.mp hm).1, (mem_Ioc.mp hm).2.trans (min_le_left _ _)⟩)
    hUV (fun m => N / m)
    (fun m => ((cutoff (μ : ArithmeticFunction ℝ) U * cutoff Λ V) m : ℂ))
    (Real.log (U * V)) ?_ ?_
  · simpa only [Nat.cast_mul] using Real.log_natCast_nonneg (U * V)
  · intro m hm
    rw [Complex.norm_real, Real.norm_eq_abs]
    apply (abs_typeI_coefficient_le_log U V m).trans
    apply Real.log_le_log (Nat.cast_pos.mpr (mem_Ioc.mp hm).1)
    exact_mod_cast (mem_Ioc.mp hm).2.trans (min_le_left _ _)

lemma expSum_add (f g : ArithmeticFunction ℝ) (θ : ℝ) (N : ℕ) :
    expSum (f + g) θ N = expSum f θ N + expSum g θ N := by
  simp only [expSum, ArithmeticFunction.add_apply, Complex.ofReal_add, add_mul,
    sum_add_distrib]

lemma expSum_sub (f g : ArithmeticFunction ℝ) (θ : ℝ) (N : ℕ) :
    expSum (f - g) θ N = expSum f θ N - expSum g θ N := by
  simp only [expSum, Erdos972Vaughan.sub_apply, Complex.ofReal_sub, sub_mul,
    sum_sub_distrib]

lemma expSum_cutoff (f : ArithmeticFunction ℝ) (U : ℕ) (θ : ℝ) (N : ℕ) :
    expSum (cutoff f U) θ N = expSum f θ (min U N) := by
  classical
  unfold expSum
  simp only [cutoff_apply, apply_ite Complex.ofReal, Complex.ofReal_zero, ite_mul, zero_mul]
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, mem_Ioc, le_min_iff]
  tauto

lemma norm_expSum_vonMangoldt_le_psi (θ : ℝ) (N : ℕ) :
    ‖expSum Λ θ N‖ ≤ Chebyshev.psi N := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ‖(Λ n : ℂ) * phase (θ * n)‖ := norm_sum_le _ _
    _ = _ := by
      simp only [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg vonMangoldt_nonneg, Chebyshev.psi, Nat.floor_natCast]

lemma norm_expSum_cutoff_vonMangoldt_le (V : ℕ) (θ : ℝ) (N : ℕ) :
    ‖expSum (cutoff Λ V) θ N‖ ≤ Chebyshev.psi V := by
  rw [expSum_cutoff]
  exact (norm_expSum_vonMangoldt_le_psi θ (min V N)).trans
    (Chebyshev.psi_mono (Nat.cast_le.mpr (min_le_left _ _)))

/-- All terms except the large-variable remainder are now estimated. -/
theorem vaughan_bound_with_remainder {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (U V N : ℕ) (hU : 8 * U ≤ q) (hUV : 8 * (U * V) ≤ q) :
    ‖expSum Λ θ N‖ ≤
      4 * Real.log (N + 1) * q * (2 + Real.log q) +
      2 * Real.log (U * V) * q * (2 + Real.log q) +
      Chebyshev.psi V +
      ‖expSum (tail (μ : ArithmeticFunction ℝ) U * ζ * tail Λ V) θ N‖ := by
  have he := congrArg (fun f => expSum f θ N) (vaughan_identity U V)
  simp only [expSum_add, expSum_sub] at he
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add _ le_rfl
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_sub_le _ _).trans
    exact add_le_add (vaughan_first_typeI_bound a haq θ hθ U N hU)
      (vaughan_second_typeI_bound a haq θ hθ U V N hUV)
  · exact norm_expSum_cutoff_vonMangoldt_le V θ N

/-- The large Möbius coefficient has a logarithmic mean-square bound. -/
theorem typeII_moebius_energy_le (U M : ℕ) :
    (∑ m ∈ Ioc 0 M, ‖((tail (μ : ArithmeticFunction ℝ) U * ζ) m : ℂ)‖ ^ 2) ≤
      (M : ℝ) * (1 + Real.log M) ^ 3 := by
  apply le_trans _ (sum_card_divisors_square_le_log M)
  apply sum_le_sum
  intro m hm
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_typeII_coefficient_le_card_divisors U m) 2

/-- A sufficient mean-square bound for the large Mangoldt coefficient. -/
theorem typeII_mangoldt_energy_le (V M : ℕ) :
    (∑ m ∈ Ioc 0 M, ‖(tail Λ V m : ℂ)‖ ^ 2) ≤
      (M : ℝ) * (Real.log M) ^ 2 := by
  calc
    _ ≤ ∑ m ∈ Ioc 0 M, (Real.log M) ^ 2 := by
      apply sum_le_sum
      intro m hm
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tail_vonMangoldt_nonneg V m)]
      apply pow_le_pow_left₀ (tail_vonMangoldt_nonneg V m)
      exact (tail_vonMangoldt_le V m).trans (vonMangoldt_le_log.trans
        (Real.log_le_log (Nat.cast_pos.mpr (mem_Ioc.mp hm).1)
          (Nat.cast_le.mpr (mem_Ioc.mp hm).2)))
    _ = _ := by simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]

/-- The local hyperbolic Type-II estimate, using mean-square coefficient bounds
rather than pointwise divisor estimates. -/
theorem vaughan_typeII_rectangle_bound {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ) (U V : ℕ)
    (s t : Finset ℕ) (M N X : ℕ) (hM : 0 < M) (hN : 0 < N)
    (herror : |θ - (a : ℝ) / q| * M * N ≤ 1)
    (hs : ∀ m ∈ s, 0 < m ∧ m ≤ M)
    (ht : ∀ n ∈ t, 0 < n ∧ n ≤ N) :
    ‖∑ m ∈ s, ∑ n ∈ t.filter (fun n => m * n ≤ X),
        ((tail (μ : ArithmeticFunction ℝ) U * ζ) m : ℂ) *
        (tail Λ V n : ℂ) * phase (θ * m * n)‖ ≤
      (2 + Real.log (N + 1)) * (Real.exp (2 * Real.pi) *
        Real.sqrt ((q : ℝ) * ((M / q + 1 : ℕ) * ((M : ℝ) * (1 + Real.log M) ^ 3)) *
          ((N / q + 1 : ℕ) * ((N : ℝ) * (Real.log N) ^ 2)))) := by
  have hleft :
      (∑ m ∈ s, ‖((tail (μ : ArithmeticFunction ℝ) U * ζ) m : ℂ)‖ ^ 2) ≤
        (M : ℝ) * (1 + Real.log M) ^ 3 := by
    apply le_trans _ (typeII_moebius_energy_le U M)
    apply sum_le_sum_of_subset_of_nonneg
    · intro m hm
      exact mem_Ioc.mpr (hs m hm)
    · intro m hm hnot
      exact sq_nonneg _
  have hright : (∑ n ∈ t, ‖(tail Λ V n : ℂ)‖ ^ 2) ≤
      (N : ℝ) * (Real.log N) ^ 2 := by
    apply le_trans _ (typeII_mangoldt_energy_le V N)
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact mem_Ioc.mpr (ht n hn)
    · intro n hn hnot
      exact sq_nonneg _
  apply (near_rational_hyperbola_energy_bound a haq θ s t M N X hM hN herror hs
    (fun n hn => (ht n hn).2)
    (fun m => ((tail (μ : ArithmeticFunction ℝ) U * ζ) m : ℂ))
    (fun n => (tail Λ V n : ℂ))).trans
  apply mul_le_mul_of_nonneg_left _ (by
    have hlog : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
    linarith)
  apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt _) (by positivity)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hleft (Nat.cast_nonneg _)) (Nat.cast_nonneg q))
    (mul_le_mul_of_nonneg_left hright (Nat.cast_nonneg _)) (by positivity)
    (by have := Real.log_natCast_nonneg M; positivity)

lemma sum_Ioc_dyadic {E : Type*} [AddCommMonoid E]
    (F : ℕ → E) (U J : ℕ) :
    (∑ m ∈ Ioc U (U * 2 ^ J), F m) =
      ∑ j ∈ range J, ∑ m ∈ Ioc (U * 2 ^ j) (U * 2 ^ (j + 1)), F m := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, ← ih]
    symm
    apply sum_Ioc_consecutive
    · exact Nat.le_mul_of_pos_right U (by positivity)
    · rw [pow_succ, ← Nat.mul_assoc]
      omega

lemma sum_Ioc_dyadic_truncated {E : Type*} [AddCommMonoid E]
    (F : ℕ → E) (U B J : ℕ) (hJ : B ≤ U * 2 ^ J) :
    (∑ m ∈ Ioc U B, F m) =
      ∑ j ∈ range J, ∑ m ∈ (Ioc (U * 2 ^ j) (U * 2 ^ (j + 1))).filter
        (fun m => m ≤ B), F m := by
  classical
  have he : (Ioc U (U * 2 ^ J)).filter (fun m => m ≤ B) = Ioc U B := by
    ext m
    simp only [mem_filter, mem_Ioc]
    omega
  rw [← he, sum_filter, sum_Ioc_dyadic]
  simp only [sum_filter]

lemma norm_sum_Ioc_dyadic_le {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (U B J : ℕ) (hJ : B ≤ U * 2 ^ J) (C : ℝ)
    (hC : ∀ j < J, ‖∑ m ∈ (Ioc (U * 2 ^ j) (U * 2 ^ (j + 1))).filter
        (fun m => m ≤ B), F m‖ ≤ C) :
    ‖∑ m ∈ Ioc U B, F m‖ ≤ (J : ℝ) * C := by
  rw [sum_Ioc_dyadic_truncated F U B J hJ]
  calc
    _ ≤ ∑ j ∈ range J, ‖∑ m ∈ (Ioc (U * 2 ^ j) (U * 2 ^ (j + 1))).filter
        (fun m => m ≤ B), F m‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range J, C := sum_le_sum (fun j hj => hC j (mem_range.mp hj))
    _ = _ := by simp

lemma tail_inner_sum_eq_zero (V X m : ℕ) (hm : X / (V + 1) < m) (θ : ℝ) :
    (∑ n ∈ Ioc 0 (X / m), (tail Λ V n : ℂ) * phase (θ * m * n)) = 0 := by
  apply sum_eq_zero
  intro n hn
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hm
  have hX : X < m * (V + 1) := (Nat.div_lt_iff_lt_mul (by omega)).mp hm
  have hnV : n ≤ V := by
    have hprod := (Nat.le_div_iff_mul_le hm0).mp (mem_Ioc.mp hn).2
    by_contra hnV
    have := Nat.mul_le_mul_left m (Nat.succ_le_of_lt (Nat.lt_of_not_ge hnV))
    nlinarith
  rw [tail_eq_zero_of_le _ hnV, Complex.ofReal_zero, zero_mul]

/-- Exact support of the large-variable term in its outer index. -/
lemma vaughan_remainder_eq_sum (U V X : ℕ) (θ : ℝ) :
    expSum (tail (μ : ArithmeticFunction ℝ) U * ζ * tail Λ V) θ X =
      ∑ m ∈ Ioc U (X / (V + 1)),
        ((tail (μ : ArithmeticFunction ℝ) U * ζ) m : ℂ) *
        ∑ n ∈ Ioc 0 (X / m), (tail Λ V n : ℂ) * phase (θ * m * n) := by
  rw [expSum_convolution]
  symm
  apply sum_subset
  · intro m hm
    exact mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.zero_le U) (mem_Ioc.mp hm).1,
      (mem_Ioc.mp hm).2.trans (Nat.div_le_self X (V + 1))⟩
  · intro m hm hnot
    by_cases hU : m ≤ U
    · rw [tail_mul_zeta_eq_zero_of_le _ U m hU, Complex.ofReal_zero, zero_mul]
    · have hB : X / (V + 1) < m := by
        simp only [mem_Ioc] at hnot
        omega
      rw [tail_inner_sum_eq_zero V X m hB θ, mul_zero]

/-- On a dyadic block, the varying inner prefixes are one hyperbolic cutoff
of a rectangle whose coordinate product is at most twice the total scale. -/
lemma vaughan_block_eq_rectangle (U V X L : ℕ) (hL : 0 < L)
    (s : Finset ℕ) (hs : ∀ m ∈ s, L < m) (θ : ℝ) :
    (∑ m ∈ s, ((tail (μ : ArithmeticFunction ℝ) U * ζ) m : ℂ) *
      ∑ n ∈ Ioc 0 (X / m), (tail Λ V n : ℂ) * phase (θ * m * n)) =
    ∑ m ∈ s, ∑ n ∈ (Ioc 0 (X / L)).filter (fun n => m * n ≤ X),
      ((tail (μ : ArithmeticFunction ℝ) U * ζ) m : ℂ) *
        (tail Λ V n : ℂ) * phase (θ * m * n) := by
  apply sum_congr rfl
  intro m hm
  have hm0 : 0 < m := hL.trans (hs m hm)
  have he : (Ioc 0 (X / L)).filter (fun n => m * n ≤ X) = Ioc 0 (X / m) := by
    ext n
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨hn0, hnL⟩, hmn⟩
      exact ⟨hn0, (Nat.le_div_iff_mul_le hm0).mpr (by simpa [mul_comm] using hmn)⟩
    · rintro ⟨hn0, hnm⟩
      refine ⟨⟨hn0, hnm.trans (Nat.div_le_div_left (hs m hm).le hL)⟩, ?_⟩
      simpa only [mul_comm] using (Nat.le_div_iff_mul_le hm0).mp hnm
  rw [he, mul_sum]
  apply sum_congr rfl
  intro n hn
  ring

/-- A uniform majorant for all rectangles of bounded coordinate product. -/
lemma rectangle_majorant_le_uniform {q : ℕ} [NeZero q]
    (M N D X : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hMD : M ≤ D) (hND : N ≤ D) (hDX : D ≤ 2 * X) (hMN : M * N ≤ 2 * X) :
    (2 + Real.log (N + 1)) * (Real.exp (2 * Real.pi) *
      Real.sqrt ((q : ℝ) * ((M / q + 1 : ℕ) * ((M : ℝ) * (1 + Real.log M) ^ 3)) *
        ((N / q + 1 : ℕ) * ((N : ℝ) * (Real.log N) ^ 2)))) ≤
      Real.exp (2 * Real.pi) * (2 + Real.log (2 * X + 1)) ^ 4 *
        Real.sqrt (2 * (X : ℝ) * (2 * X / q + 2 * D + q)) := by
  let L : ℝ := 2 + Real.log (2 * X + 1)
  let T : ℝ := 2 * (X : ℝ) * (2 * X / q + 2 * D + q)
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hM0 : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hMD' : (M : ℝ) ≤ D := Nat.cast_le.mpr hMD
  have hND' : (N : ℝ) ≤ D := Nat.cast_le.mpr hND
  have hDX' : (D : ℝ) ≤ 2 * X := by exact_mod_cast hDX
  have hMN' : (M : ℝ) * N ≤ 2 * X := by exact_mod_cast hMN
  have hL : 1 ≤ L := by
    have : 0 ≤ Real.log (2 * (X : ℝ) + 1) := Real.log_nonneg (by linarith)
    dsimp [L]
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hlogM0 := Real.log_natCast_nonneg M
  have hlogN0 := Real.log_natCast_nonneg N
  have hLM : 1 + Real.log M ≤ L := by
    have := Real.log_le_log hM0 (show (M : ℝ) ≤ 2 * X + 1 by linarith)
    dsimp [L]
    linarith
  have hLN : Real.log N ≤ L := by
    have := Real.log_le_log hN0 (show (N : ℝ) ≤ 2 * X + 1 by linarith)
    dsimp [L]
    linarith
  have hcompletion : 2 + Real.log (N + 1) ≤ L := by
    have := Real.log_le_log (show (0 : ℝ) < N + 1 by linarith)
      (show (N : ℝ) + 1 ≤ 2 * X + 1 by linarith)
    dsimp [L]
    linarith
  have hdiv (a : ℕ) : ((a / q + 1 : ℕ) : ℝ) ≤ (a : ℝ) / q + 1 := by
    have hd : ((a / q : ℕ) : ℝ) ≤ (a : ℝ) / q := by
      apply (le_div_iff₀ hq).mpr
      exact_mod_cast Nat.div_mul_le_self a q
    push_cast
    linarith
  have hleft : ((M / q + 1 : ℕ) : ℝ) * ((M : ℝ) * (1 + Real.log M) ^ 3) ≤
      ((M : ℝ) / q + 1) * ((M : ℝ) * L ^ 3) := by
    exact mul_le_mul (hdiv M)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hLM 3) hM0.le)
      (by positivity) (by positivity)
  have hright : ((N / q + 1 : ℕ) : ℝ) * ((N : ℝ) * (Real.log N) ^ 2) ≤
      ((N : ℝ) / q + 1) * ((N : ℝ) * L ^ 2) := by
    exact mul_le_mul (hdiv N)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogN0 hLN 2) hN0.le)
      (by positivity) (by positivity)
  have hbase : (q : ℝ) * (((M : ℝ) / q + 1) * M) * (((N : ℝ) / q + 1) * N) ≤ T := by
    have he : (q : ℝ) * (((M : ℝ) / q + 1) * M) * (((N : ℝ) / q + 1) * N) =
        ((M : ℝ) * N) * ((M : ℝ) * N / q + M + N + q) := by
      field_simp
      ring
    rw [he]
    have hh : (M : ℝ) * N / q + M + N + q ≤ 2 * X / q + 2 * D + q := by
      have := div_le_div_of_nonneg_right hMN' hq.le
      linarith
    exact mul_le_mul hMN' hh (by positivity) (by positivity)
  have hinside :
      (q : ℝ) * ((M / q + 1 : ℕ) * ((M : ℝ) * (1 + Real.log M) ^ 3)) *
        ((N / q + 1 : ℕ) * ((N : ℝ) * (Real.log N) ^ 2)) ≤ L ^ 6 * T := by
    calc
      _ ≤ (q : ℝ) * (((M : ℝ) / q + 1) * ((M : ℝ) * L ^ 3)) *
          (((N : ℝ) / q + 1) * ((N : ℝ) * L ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hleft hq.le) hright (by positivity) (by positivity)
      _ = L ^ 5 * ((q : ℝ) * (((M : ℝ) / q + 1) * M) * (((N : ℝ) / q + 1) * N)) := by ring
      _ ≤ L ^ 5 * T := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ L ^ 6 * T := by
        apply mul_le_mul_of_nonneg_right _ hT
        simpa only [pow_succ, mul_one] using mul_le_mul_of_nonneg_left hL (pow_nonneg hL0 5)
  have hsqrt : Real.sqrt (L ^ 6 * T) = L ^ 3 * Real.sqrt T := by
    rw [show L ^ 6 = (L ^ 3) ^ 2 by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (pow_nonneg hL0 3)]
  calc
    _ ≤ L * (Real.exp (2 * Real.pi) * Real.sqrt (L ^ 6 * T)) := by
      exact mul_le_mul hcompletion
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinside) (by positivity))
        (by positivity) hL0
    _ = _ := by rw [hsqrt]; change L * (_ * (L ^ 3 * Real.sqrt T)) = _ * L ^ 4 * Real.sqrt T; ring

/-- Summing the local Type-II estimate over dyadic outer blocks. -/
theorem vaughan_typeII_dyadic_bound {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (U X J : ℕ) (hU : 0 < U) (hXq : 2 * (X : ℝ) ≤ (q : ℝ) ^ 2)
    (hJ : X / (U + 1) ≤ U * 2 ^ J) :
    ‖expSum (tail (μ : ArithmeticFunction ℝ) U * ζ * tail Λ U) θ X‖ ≤
      (J : ℝ) * (Real.exp (2 * Real.pi) * (2 + Real.log (2 * X + 1)) ^ 4 *
        Real.sqrt (2 * (X : ℝ) * (2 * X / q + 4 * (X / U : ℕ) + q))) := by
  classical
  rw [vaughan_remainder_eq_sum]
  apply norm_sum_Ioc_dyadic_le _ U (X / (U + 1)) J hJ
  intro j hj
  let L : ℕ := U * 2 ^ j
  let s : Finset ℕ := (Ioc (U * 2 ^ j) (U * 2 ^ (j + 1))).filter
    (fun m => m ≤ X / (U + 1))
  change ‖∑ m ∈ s, ((tail (μ : ArithmeticFunction ℝ) U * ζ) m : ℂ) *
    ∑ n ∈ Ioc 0 (X / m), (tail Λ U n : ℂ) * phase (θ * m * n)‖ ≤ _
  by_cases hs0 : s = ∅
  · rw [hs0, sum_empty, norm_zero]
    positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hUL : U ≤ L := Nat.le_mul_of_pos_right U (by positivity)
  have hs (m : ℕ) (hm : m ∈ s) : L < m ∧ m ≤ 2 * L ∧ m ≤ X / (U + 1) := by
    obtain ⟨hm, hB⟩ := mem_filter.mp hm
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hm
    refine ⟨hlo, ?_, hB⟩
    simpa only [L, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hhi
  obtain ⟨m, hm⟩ := nonempty_iff_ne_empty.mpr hs0
  have hLB : L ≤ X / (U + 1) := (hs m hm).1.le.trans (hs m hm).2.2
  have hLX : L ≤ X := hLB.trans (Nat.div_le_self X (U + 1))
  have hN : 0 < X / L := Nat.div_pos hLX hL
  have hM : 0 < 2 * L := by positivity
  have hLdiv : L ≤ X / U := hLB.trans (Nat.div_le_div_left (Nat.le_succ U) hU)
  have hMD : 2 * L ≤ 2 * (X / U) := Nat.mul_le_mul_left 2 hLdiv
  have hND : X / L ≤ 2 * (X / U) := by
    have := Nat.div_le_div_left hUL hU (a := X)
    omega
  have hDX : 2 * (X / U) ≤ 2 * X := Nat.mul_le_mul_left 2 (Nat.div_le_self X U)
  have hMN : (2 * L) * (X / L) ≤ 2 * X := by
    have := Nat.div_mul_le_self X L
    nlinarith
  have herror : |θ - (a : ℝ) / q| * (2 * L : ℕ) * (X / L : ℕ) ≤ 1 := by
    have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    have he := (le_div_iff₀ (sq_pos_of_pos hq)).mp hθ
    have hMN' : ((2 * L : ℕ) : ℝ) * (X / L : ℕ) ≤ 2 * X := by exact_mod_cast hMN
    have hb := mul_le_mul_of_nonneg_left (hMN'.trans hXq) (abs_nonneg (θ - (a : ℝ) / q))
    nlinarith
  rw [vaughan_block_eq_rectangle U U X L hL s (fun m hm => (hs m hm).1) θ]
  apply (vaughan_typeII_rectangle_bound a haq θ U U s (Ioc 0 (X / L)) (2 * L) (X / L) X
    hM hN herror
    (fun m hm => ⟨hL.trans (hs m hm).1, (hs m hm).2.1⟩)
    (fun n hn => mem_Ioc.mp hn)).trans
  simpa only [Nat.cast_mul, Nat.cast_ofNat, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using
    rectangle_majorant_le_uniform (q := q) (2 * L) (X / L) (2 * (X / U)) X
      hM hN hMD hND hDX hMN

/-- A completely explicit Type-II bound, with the number of blocks chosen
logarithmically. -/
theorem vaughan_typeII_bound {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (U X : ℕ) (hU : 0 < U) (hXq : 2 * (X : ℝ) ≤ (q : ℝ) ^ 2) :
    ‖expSum (tail (μ : ArithmeticFunction ℝ) U * ζ * tail Λ U) θ X‖ ≤
      (Nat.log 2 X + 1 : ℕ) *
        (Real.exp (2 * Real.pi) * (2 + Real.log (2 * X + 1)) ^ 4 *
          Real.sqrt (2 * (X : ℝ) * (2 * X / q + 4 * (X / U : ℕ) + q))) := by
  apply vaughan_typeII_dyadic_bound a haq θ hθ U X (Nat.log 2 X + 1) hU hXq
  have hpow : X < 2 ^ (Nat.log 2 X + 1) := Nat.lt_pow_succ_log_self (by norm_num) X
  exact (Nat.div_le_self X (U + 1)).trans (hpow.le.trans
    (Nat.le_mul_of_pos_left _ hU))

/-- The complete finite Vaughan estimate at the chosen rational scale. -/
theorem vonMangoldt_expSum_bound {q : ℕ} [NeZero q]
    (a : ℕ) (haq : a.Coprime q) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (U X : ℕ) (hU : 0 < U) (hUq : 8 * (U * U) ≤ q)
    (hXq : 2 * (X : ℝ) ≤ (q : ℝ) ^ 2) :
    ‖expSum Λ θ X‖ ≤
      4 * Real.log (X + 1) * q * (2 + Real.log q) +
      2 * Real.log (U * U) * q * (2 + Real.log q) + Chebyshev.psi U +
      (Nat.log 2 X + 1 : ℕ) *
        (Real.exp (2 * Real.pi) * (2 + Real.log (2 * X + 1)) ^ 4 *
          Real.sqrt (2 * (X : ℝ) * (2 * X / q + 4 * (X / U : ℕ) + q))) := by
  have hUq' : 8 * U ≤ q := (Nat.mul_le_mul_left 8 (Nat.le_mul_of_pos_right U hU)).trans hUq
  exact (vaughan_bound_with_remainder a haq θ hθ U U X hUq' hUq).trans
    (add_le_add le_rfl (vaughan_typeII_bound a haq θ hθ U X hU hXq))

#print axioms vonMangoldt_expSum_bound
#print axioms vaughan_typeII_bound
#print axioms rectangle_majorant_le_uniform
#print axioms vaughan_remainder_eq_sum
#print axioms vaughan_block_eq_rectangle
#print axioms vaughan_typeII_rectangle_bound
#print axioms vaughan_bound_with_remainder
#print axioms typeII_moebius_energy_le
#print axioms typeII_mangoldt_energy_le
#print axioms vaughan_first_typeI_bound
#print axioms vaughan_second_typeI_bound
end Erdos972VaughanSums
