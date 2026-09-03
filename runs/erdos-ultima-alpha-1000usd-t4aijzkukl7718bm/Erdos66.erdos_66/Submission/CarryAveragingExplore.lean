import FormalConjecturesUtil

/-!
# Averaging the carry in a thickened two-coordinate digit encoding

The estimates here concern finite counting kernels. They do not supply an
infinite set of natural numbers for Erdős Problem 66.
-/
namespace Erdos66CarryAveraging

/-- The integer triangular kernel; integer indices are essential at `z = -1`. -/
def triangle (K : ℕ) (z : ℤ) : ℤ :=
  max 0 (min (z + 1) (2 * (K : ℤ) - 1 - z))

lemma triangle_nonneg (K : ℕ) (z : ℤ) : 0 ≤ triangle K z := le_max_left _ _

lemma triangle_step (K : ℕ) (z : ℤ) :
    |triangle K z - triangle K (z - 1)| ≤ 1 := by
  rw [abs_le]
  unfold triangle
  constructor <;> omega

lemma triangle_period (K q : ℕ) (hq : q < K) :
    triangle K q + triangle K ((q : ℤ) + K) = K := by
  unfold triangle
  omega

/-- The kernel is precisely an ordered pair count in an interval. -/
lemma triangle_count (K : ℕ) (z : ℤ) :
    (((Finset.range K ×ˢ Finset.range K).filter
      (fun ab ↦ (ab.1 : ℤ) + ab.2 = z)).card : ℤ) = triangle K z := by
  classical
  let S := Finset.Icc (max 0 (z - K + 1)) (min ((K : ℤ) - 1) z)
  have hc : ((Finset.range K ×ˢ Finset.range K).filter
      (fun ab ↦ (ab.1 : ℤ) + ab.2 = z)).card = S.card := by
    apply Finset.card_bij (fun ab _ ↦ (ab.1 : ℤ))
    · intro ab hab
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab
      simp only [S, Finset.mem_Icc]
      omega
    · intro ab hab cd hcd heq
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hab hcd
      apply Prod.ext <;> dsimp at * <;> omega
    · intro x hx
      simp only [S, Finset.mem_Icc] at hx
      refine ⟨(x.toNat, (z - x).toNat), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        omega
      · dsimp
        omega
  rw [hc]
  dsimp [S]
  rw [Int.card_Icc]
  unfold triangle
  omega

/-- A carry changes each triangular weight by at most one. -/
lemma weighted_carry_error {ι : Type*} (s : Finset ι) (e : ι → ℤ)
    (he : ∀ i ∈ s, e i = 0 ∨ e i = 1) (K : ℕ) (z : ℤ) :
    |(∑ i ∈ s, (triangle K (z - e i) : ℝ)) -
      (s.card : ℝ) * (triangle K z : ℝ)| ≤ s.card := by
  classical
  have hstep : ∀ i ∈ s,
      |(triangle K (z - e i) : ℝ) - (triangle K z : ℝ)| ≤ 1 := by
    intro i hi
    rcases he i hi with h | h
    · simp [h]
    · rw [h, abs_sub_comm]
      exact_mod_cast triangle_step K z
  calc
    _ = |∑ i ∈ s, ((triangle K (z - e i) : ℝ) - (triangle K z : ℝ))| := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, |(triangle K (z - e i) : ℝ) - (triangle K z : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, (1 : ℝ) := Finset.sum_le_sum hstep
    _ = s.card := by simp

/-- Abstract version of the carry-averaging estimate. The two fibers may have
arbitrary distributions between the two small carry values. -/
lemma two_fiber_error {ι : Type*} (s₀ s₁ : Finset ι) (e : ι → ℤ)
    (he₀ : ∀ i ∈ s₀, e i = 0 ∨ e i = 1)
    (he₁ : ∀ i ∈ s₁, e i = 0 ∨ e i = 1)
    (K q : ℕ) (hq : q < K) (μ E : ℝ)
    (h₀ : |(s₀.card : ℝ) - μ| ≤ E) (h₁ : |(s₁.card : ℝ) - μ| ≤ E) :
    |(K : ℝ) * ((∑ i ∈ s₀, (triangle K ((q : ℤ) - e i) : ℝ)) +
        ∑ i ∈ s₁, (triangle K ((q : ℤ) + K - e i) : ℝ)) -
      (K : ℝ) ^ 2 * μ| ≤ (K : ℝ) ^ 2 * E + 2 * K * (μ + E) := by
  have hc₀ := weighted_carry_error s₀ e he₀ K q
  have hc₁ := weighted_carry_error s₁ e he₁ K ((q : ℤ) + K)
  have ht : (triangle K q : ℝ) + (triangle K ((q : ℤ) + K) : ℝ) = K := by
    exact_mod_cast triangle_period K q hq
  have ht₀ : 0 ≤ (triangle K q : ℝ) := by exact_mod_cast triangle_nonneg K q
  have ht₁ : 0 ≤ (triangle K ((q : ℤ) + K) : ℝ) := by
    exact_mod_cast triangle_nonneg K ((q : ℤ) + K)
  have hk : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hf₀ : |((s₀.card : ℝ) - μ) * (triangle K q : ℝ)| ≤
      E * (triangle K q : ℝ) := by
    rw [abs_mul, abs_of_nonneg ht₀]
    exact mul_le_mul_of_nonneg_right h₀ ht₀
  have hf₁ : |((s₁.card : ℝ) - μ) * (triangle K ((q : ℤ) + K) : ℝ)| ≤
      E * (triangle K ((q : ℤ) + K) : ℝ) := by
    rw [abs_mul, abs_of_nonneg ht₁]
    exact mul_le_mul_of_nonneg_right h₁ ht₁
  have hs₀ := (abs_le.mp h₀).2
  have hs₁ := (abs_le.mp h₁).2
  have hav :
      |((∑ i ∈ s₀, (triangle K ((q : ℤ) - e i) : ℝ)) +
          ∑ i ∈ s₁, (triangle K ((q : ℤ) + K - e i) : ℝ)) - (K : ℝ) * μ| ≤
        (K : ℝ) * E + 2 * (μ + E) := by
    have ha := abs_add_le
      ((∑ i ∈ s₀, (triangle K ((q : ℤ) - e i) : ℝ)) -
        (s₀.card : ℝ) * (triangle K q : ℝ))
      ((∑ i ∈ s₁, (triangle K ((q : ℤ) + K - e i) : ℝ)) -
        (s₁.card : ℝ) * (triangle K ((q : ℤ) + K) : ℝ))
    have hb := abs_add_le
      (((s₀.card : ℝ) - μ) * (triangle K q : ℝ))
      (((s₁.card : ℝ) - μ) * (triangle K ((q : ℤ) + K) : ℝ))
    have hd := abs_add_le
      (((∑ i ∈ s₀, (triangle K ((q : ℤ) - e i) : ℝ)) -
          (s₀.card : ℝ) * (triangle K q : ℝ)) +
        ((∑ i ∈ s₁, (triangle K ((q : ℤ) + K - e i) : ℝ)) -
          (s₁.card : ℝ) * (triangle K ((q : ℤ) + K) : ℝ)))
      ((((s₀.card : ℝ) - μ) * (triangle K q : ℝ)) +
        (((s₁.card : ℝ) - μ) * (triangle K ((q : ℤ) + K) : ℝ)))
    have hid :
        (((∑ i ∈ s₀, (triangle K ((q : ℤ) - e i) : ℝ)) -
          (s₀.card : ℝ) * (triangle K q : ℝ)) +
        ((∑ i ∈ s₁, (triangle K ((q : ℤ) + K - e i) : ℝ)) -
          (s₁.card : ℝ) * (triangle K ((q : ℤ) + K) : ℝ))) +
        ((((s₀.card : ℝ) - μ) * (triangle K q : ℝ)) +
        (((s₁.card : ℝ) - μ) * (triangle K ((q : ℤ) + K) : ℝ))) =
        ((∑ i ∈ s₀, (triangle K ((q : ℤ) - e i) : ℝ)) +
          ∑ i ∈ s₁, (triangle K ((q : ℤ) + K - e i) : ℝ)) - (K : ℝ) * μ := by
      linear_combination -μ * ht
    rw [hid] at hd
    nlinarith [ha, hb, hd]
  calc
    _ = (K : ℝ) * |((∑ i ∈ s₀, (triangle K ((q : ℤ) - e i) : ℝ)) +
        ∑ i ∈ s₁, (triangle K ((q : ℤ) + K - e i) : ℝ)) - (K : ℝ) * μ| := by
      rw [show (K : ℝ) * ((∑ i ∈ s₀, (triangle K ((q : ℤ) - e i) : ℝ)) +
          ∑ i ∈ s₁, (triangle K ((q : ℤ) + K - e i) : ℝ)) - (K : ℝ) ^ 2 * μ =
          (K : ℝ) * (((∑ i ∈ s₀, (triangle K ((q : ℤ) - e i) : ℝ)) +
          ∑ i ∈ s₁, (triangle K ((q : ℤ) + K - e i) : ℝ)) - (K : ℝ) * μ) by ring,
        abs_mul, abs_of_nonneg hk]
    _ ≤ (K : ℝ) * ((K : ℝ) * E + 2 * (μ + E)) := mul_le_mul_of_nonneg_left hav hk
    _ = _ := by ring

end Erdos66CarryAveraging
