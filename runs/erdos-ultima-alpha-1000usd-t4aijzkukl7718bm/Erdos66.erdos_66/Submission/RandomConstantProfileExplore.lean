import Submission.FiniteRepBernoulliExplore
import Submission.ShiftedProfileExplore

/-! Finite binary sets with nearly constant representation counts on a long
interval, using a shifted binomial probability profile. -/
namespace Erdos66RandomConstantProfile
open AdditiveCombinatorics Erdos66FiniteRepBernoulli Erdos66ConstantProfile
  Erdos66ShiftedProfile
open scoped Classical
set_option maxHeartbeats 800000

noncomputable def probability (μ : ℝ) (s L : ℕ) (i : Fin (L + 1)) : ℝ :=
  Real.sqrt μ * b (i.val + s)

lemma probability_bounds (μ : ℝ) (s L : ℕ) (hμ : 0 ≤ μ) (hs : μ ≤ (s : ℝ) + 1)
    (i : Fin (L + 1)) : 0 ≤ probability μ s L i ∧ probability μ s L i ≤ 1 := by
  have hp := (b_pos (i.val + s)).le
  have hsqrt := Real.sqrt_nonneg μ
  have hb := b_square_bound (i.val + s)
  have hscale : μ * b (i.val + s) ^ 2 ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right (show μ ≤ (i.val + s : ℕ) + (1 : ℝ) by
      push_cast; linarith [Nat.cast_nonneg (α := ℝ) i.val]) (sq_nonneg (b (i.val + s)))
    exact hh.trans hb
  have hsq : (Real.sqrt μ * b (i.val + s)) ^ 2 ≤ 1 := by
    rw [mul_pow, Real.sq_sqrt hμ]
    exact hscale
  dsimp [probability]
  exact ⟨mul_nonneg hsqrt hp, by nlinarith [mul_nonneg hsqrt hp]⟩

lemma full_mean_upper (μ : ℝ) (s L q : ℕ) (hμ : 0 ≤ μ) :
    (∑ a ∈ pairs L q, probability μ s L a.1 * probability μ s L a.2) ≤ μ := by
  have hprod (a : Fin (L + 1) × Fin (L + 1)) :
      probability μ s L a.1 * probability μ s L a.2 = μ * (b (a.1.val + s) * b (a.2.val + s)) := by
    dsimp [probability]
    calc
      _ = (Real.sqrt μ) ^ 2 * (b (a.1.val + s) * b (a.2.val + s)) := by ring
      _ = _ := by rw [Real.sq_sqrt hμ]
  simp_rw [hprod]
  rw [pairs_sum_range L q (fun i j ↦ μ * (b (i + s) * b (j + s)))]
  have hh : (∑ k ∈ Finset.range (q + 1),
      if k ≤ L ∧ q - k ≤ L then μ * (b (k + s) * b (q - k + s)) else 0) ≤
      μ * tailConv s q := by
    rw [tailConv, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    split_ifs
    · rfl
    · exact mul_nonneg hμ (mul_nonneg (b_pos _).le (b_pos _).le)
  exact hh.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (tailConv_upper s q) hμ)

lemma full_mean_eq (μ : ℝ) (s L q : ℕ) (hμ : 0 ≤ μ) (hq : q ≤ L) :
    (∑ a ∈ pairs L q, probability μ s L a.1 * probability μ s L a.2) = μ * tailConv s q := by
  have hprod (a : Fin (L + 1) × Fin (L + 1)) :
      probability μ s L a.1 * probability μ s L a.2 = μ * (b (a.1.val + s) * b (a.2.val + s)) := by
    dsimp [probability]
    calc
      _ = (Real.sqrt μ) ^ 2 * (b (a.1.val + s) * b (a.2.val + s)) := by ring
      _ = _ := by rw [Real.sq_sqrt hμ]
  simp_rw [hprod]
  rw [pairs_sum_range L q (fun i j ↦ μ * (b (i + s) * b (j + s))), tailConv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_pos ⟨by have hh := Finset.mem_range.mp hk; omega, by omega⟩]

lemma mean_upper (μ : ℝ) (s L q : ℕ) (hμ : 0 ≤ μ) (hs : μ ≤ (s : ℝ) + 1) :
    repMean L q (probability μ s L) ≤ μ + 1 := by
  rw [mean_decomposition]
  exact add_le_add (full_mean_upper μ s L q hμ)
    (diagCorrection_bounds L q _ (probability_bounds μ s L hμ hs)).2

lemma mean_lower (μ : ℝ) (s L q : ℕ) (hμ : 0 ≤ μ) (hs : μ ≤ (s : ℝ) + 1) (hq : q ≤ L) :
    μ * (1 - 2 * s * b q) ≤ repMean L q (probability μ s L) := by
  rw [mean_decomposition, full_mean_eq μ s L q hμ hq]
  have hh := mul_le_mul_of_nonneg_left (tailConv_lower s q) hμ
  have hd := (diagCorrection_bounds L q _ (probability_bounds μ s L hμ hs)).1
  linarith

lemma profile_tail_small (s q₀ q : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hq : q₀ ≤ q)
    (hstart : 64 * (s : ℝ) ^ 2 ≤ ε ^ 2 * (q₀ + 1)) :
    2 * (s : ℝ) * b q ≤ ε / 4 := by
  have hb := b_square_bound q
  have hq' : (q₀ : ℝ) + 1 ≤ q + 1 := by exact_mod_cast Nat.add_le_add_right hq 1
  have hbound := hstart.trans (mul_le_mul_of_nonneg_left hq' (sq_nonneg ε))
  have h₁ := mul_le_mul_of_nonneg_right hbound (sq_nonneg (b q))
  have h₂ := mul_le_mul_of_nonneg_left hb (sq_nonneg ε)
  have hpos : 0 ≤ 2 * (s : ℝ) * b q := mul_nonneg (by positivity) (b_pos _).le
  nlinarith [sq_nonneg (2 * (s : ℝ) * b q - ε / 4)]

lemma rep_zero_above_support (D : Set ℕ) (L q : ℕ) (hD : ∀ n ∈ D, n ≤ L) (hq : 2 * L < q) :
    sumRep D q = 0 := by
  rw [sumRep_def, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨hsum, h₁, h₂⟩ := Finset.mem_filter.mp ha
  have he := Finset.mem_antidiagonal.mp hsum
  have hl₁ := hD a.1 h₁
  have hl₂ := hD a.2 h₂
  omega

/-- The logarithm of the available cutoff may be proportional to the desired
mean. This is a finite statement; no compatible infinite set is asserted. -/
theorem exists_constant_profile (μ ε : ℝ) (s q₀ L : ℕ)
    (hμ : 1 ≤ μ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hlarge : 4 ≤ ε * μ)
    (hs : μ ≤ (s : ℝ) + 1)
    (hstart : 64 * (s : ℝ) ^ 2 ≤ ε ^ 2 * (q₀ + 1))
    (hsmall : 2 * (2 * (L : ℝ) + 1) * Real.exp (-ε ^ 2 * (μ + 1) / 128) < 1) :
    ∃ D : Set ℕ, D.Finite ∧ (∀ n ∈ D, n ≤ L) ∧
      (∀ q : ℕ, (sumRep D q : ℝ) ≤ (1 + ε) * μ) ∧
      ∀ q : ℕ, q₀ ≤ q → q ≤ L → |(sumRep D q : ℝ) - μ| < ε * μ := by
  have hμ0 : 0 ≤ μ := by linarith
  have hsmall' : 2 * ((2 * L : ℕ) + 1 : ℝ) * Real.exp (-(ε / 4) ^ 2 * (μ + 1) / 8) < 1 := by
    convert hsmall using 1 <;> push_cast <;> congr 2 <;> ring
  obtain ⟨D, hDfin, hD, hrep⟩ := exists_simultaneous_rep_bound L (2 * L)
    (probability μ s L) (probability_bounds μ s L hμ0 hs) (μ + 1) (ε / 4)
    (by linarith) (by positivity) (by linarith) (fun q _ ↦ mean_upper μ s L q hμ0 hs) hsmall'
  have hdev : ε / 4 * (μ + 1) ≤ ε * μ / 2 := by nlinarith
  refine ⟨D, hDfin, hD, ?_, ?_⟩
  · intro q
    by_cases hq : q ≤ 2 * L
    · have hh := (abs_lt.mp (hrep q hq)).2
      have hm := mean_upper μ s L q hμ0 hs
      nlinarith
    · rw [rep_zero_above_support D L q hD (by omega), Nat.cast_zero]
      positivity
  · intro q hq₀ hq
    have hh := hrep q (by omega)
    have hl := mean_lower μ s L q hμ0 hs hq
    have hu := mean_upper μ s L q hμ0 hs
    have ht := profile_tail_small s q₀ q ε hε.le hq₀ hstart
    have hb := mul_le_mul_of_nonneg_left ht hμ0
    rw [abs_lt] at hh ⊢
    constructor <;> nlinarith

end Erdos66RandomConstantProfile
