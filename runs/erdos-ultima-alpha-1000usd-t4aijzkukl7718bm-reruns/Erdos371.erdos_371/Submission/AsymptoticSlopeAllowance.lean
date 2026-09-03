import FormalConjecturesUtil
import Submission.TwoSidedPrimeDeletion

/-! A weaker sufficient criterion for Erdős 371: a vanishing one-sided
allowance along the prime slopes, with a separate asymptotic threshold for
each slope. The arithmetic hypotheses are not proved in this file. -/

namespace Erdos371AsymptoticSlopeAllowance

open Finset Filter Erdos371SmallPrimeAveraging Erdos371PrimeDeletion
open Erdos371PrimeDeletionVariance Erdos371TwoSidedPrimeDeletion
open scoped Topology

noncomputable def minusPrefix (p A : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 A, Erdos371PrimeDeletion.compare (P (a*p-1)) (P a)

noncomputable def plusPrefix (p A : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 A, Erdos371PrimeDeletion.compare (P (a*p+1)) (P a)

lemma large_prime_mass_unbounded (Y : ℕ) (B : ℝ) :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ Y ≤ p) ∧ B < mass s := by
  obtain ⟨t, ht, hB⟩ := Erdos371AveragingCriterion.prime_mass_unbounded
    (B + mass (range Y))
  let s := t.filter (fun p => Y ≤ p)
  let r := t.filter (fun p => ¬ Y ≤ p)
  have he : mass s + mass r = mass t :=
    sum_filter_add_sum_filter_not t (fun p => Y ≤ p) (fun p => 1/(p:ℝ))
  have hr : mass r ≤ mass (range Y) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨_, hp⟩ := mem_filter.mp hp
      exact mem_range.mpr (by omega)
    · intro p _ _
      positivity
  refine ⟨s, ?_, ?_⟩
  · intro p hp
    exact ⟨ht p (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
  · linarith

lemma divided_prefix_bound (s : Finset ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (F : ℕ → ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    (h : ∀ p ∈ s, F p (N/p) ≤ δ*(N/p:ℕ)) :
    (∑ p ∈ s, F p (N/p)) / N ≤ δ * mass s := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ ∑ p ∈ s, δ * ((N:ℝ)/p) := by
      apply sum_le_sum
      intro p hp
      exact (h p hp).trans (mul_le_mul_of_nonneg_left Nat.cast_div_le hδ)
    _ = δ * mass s * N := by
      unfold mass
      simp only [mul_sum, sum_mul]
      apply sum_congr rfl
      intro p hp
      ring

lemma right_mean_eq (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (N : ℕ) :
    mean (rightDeleted s) N = (∑ p ∈ s, minusPrefix p (N/p)) / N := by
  unfold mean
  rw [rightDeleted_sum_eq_affine s hs N]
  rfl

lemma after_mean_eq (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (N : ℕ) :
    mean (afterDeleted s) N = (∑ p ∈ s, plusPrefix p (N/p)) / N := by
  unfold mean afterDeleted
  rw [sum_comm]
  congr 1
  exact sum_congr rfl (fun p hp => after_prime_reindex (hs p hp).pos N)

/-- The thresholds in `A` may depend on the slope `p`. Only the eventual
upper allowances must tend to zero along the primes. -/
theorem density_half_of_eventual_slope_allowance
    (h : ∀ δ : ℝ, 0 < δ → ∃ Y : ℕ, ∀ p : ℕ, p.Prime → Y ≤ p →
      ∀ᶠ A in atTop, minusPrefix p A ≤ δ*A ∧ plusPrefix p A ≤ δ*A) :
    {n | Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)}.HasDensity (1/2) := by
  rw [Erdos371PrimeDiscrepancy.density_half_iff_total_mean_zero,
    Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨Y, hY⟩ := h (ε/4) (by positivity)
  obtain ⟨s, hs, hM⟩ := large_prime_mass_unbounded Y
    (max (48/ε^2) (8/ε))
  let M := mass s
  have hM₁ : 48/ε^2 < M := (le_max_left _ _).trans_lt hM
  have hM₂ : 8/ε < M := (le_max_right _ _).trans_lt hM
  have hM0 : 0 < M := (div_pos (by norm_num) hε).trans hM₂
  have hroot : Real.sqrt (3*M) + 2 < M*ε/2 := by
    have h₁ : 48 < M*ε^2 := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hM₁
    have h₂ : 8 < M*ε := (div_lt_iff₀ hε).mp hM₂
    have hsqrt : Real.sqrt (3*M) < M*ε/4 := by
      apply (Real.sqrt_lt' (by positivity)).mpr
      have hh := mul_lt_mul_of_pos_left h₁ hM0
      nlinarith
    linarith
  have hpref : ∀ᶠ N in atTop, ∀ p ∈ s,
      minusPrefix p (N/p) ≤ (ε/4)*(N/p:ℕ) ∧
      plusPrefix p (N/p) ≤ (ε/4)*(N/p:ℕ) := by
    apply (eventually_all_finset s).mpr
    intro p hp
    exact (Nat.tendsto_div_const_atTop (hs p hp).1.ne_zero).eventually
      (hY p (hs p hp).1 (hs p hp).2)
  have hboundary : ∀ᶠ N : ℕ in atTop, (2:ℝ)/N < ε/4 :=
    (tendsto_natCast_atTop_atTop.const_div_atTop (2:ℝ)).eventually_lt_const
      (by positivity)
  filter_upwards [hpref, hboundary, eventually_ge_atTop s.card,
    eventually_gt_atTop 0] with N hpreN hboundaryN hcard hN
  rw [Real.dist_eq, sub_zero]
  have hpr : ∀ p ∈ s, p.Prime := fun p hp => (hs p hp).1
  have hm : mean (rightDeleted s) N ≤ (ε/4)*M := by
    rw [right_mean_eq s hpr]
    exact divided_prefix_bound s (by positivity) minusPrefix hN
      (fun p hp => (hpreN p hp).1)
  have hp : mean (afterDeleted s) N ≤ (ε/4)*M := by
    rw [after_mean_eq s hpr]
    exact divided_prefix_bound s (by positivity) plusPrefix hN
      (fun p hp => (hpreN p hp).2)
  have hv : Real.sqrt (varianceMean s N) ≤ Real.sqrt (3*M) :=
    Real.sqrt_le_sqrt (varianceMean_le_three_mass s hpr N hcard)
  have hright := (signed_mean_approximation s hpr N).trans
    (add_le_add hv (le_refl 2))
  have hafter := (after_mean_approximation s hpr N).trans
    (add_le_add hv (le_refl 2))
  have hb := afterSign_mean_boundary N
  let D : ℝ := (Erdos371PrimeDiscrepancy.total N : ℝ)/N
  have hd₁ : M*D - mean (rightDeleted s) N ≤ Real.sqrt (3*M)+2 := by
    simpa only [D, M, mul_div_assoc] using (abs_le.mp hright).2
  have hd₂ : M*mean afterSign N - mean (afterDeleted s) N ≤ Real.sqrt (3*M)+2 :=
    (abs_le.mp hafter).2
  have hd₃ : -(2/(N:ℝ)) ≤ mean afterSign N + D := (abs_le.mp hb).1
  have hb' : M*(2/(N:ℝ)) < M*(ε/4) := mul_lt_mul_of_pos_left hboundaryN hM0
  have hsum : -M*D ≤ M*mean afterSign N + M*(2/(N:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hd₃ hM0.le
    nlinarith
  have hupper : D < ε := by
    have hh : M*D < M*ε := by nlinarith
    exact (mul_lt_mul_iff_right₀ hM0).mp hh
  have hlower : -ε < D := by
    have hh : M*(-ε) < M*D := by nlinarith
    exact (mul_lt_mul_iff_right₀ hM0).mp hh
  exact abs_lt.mpr ⟨hlower,hupper⟩

/-- In particular, a bound `c(p) A + o_p(A)` for both signs is sufficient
when `c(p)` tends to zero. No uniformity of the `o_p(A)` threshold is required. -/
theorem density_half_of_asymptotic_slope_allowance (c : ℕ → ℝ)
    (hc : Tendsto c atTop (𝓝 0))
    (h : ∀ p : ℕ, p.Prime → ∀ η : ℝ, 0 < η →
      ∀ᶠ A in atTop, minusPrefix p A ≤ (c p+η)*A ∧
        plusPrefix p A ≤ (c p+η)*A) :
    {n | Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)}.HasDensity (1/2) := by
  apply density_half_of_eventual_slope_allowance
  intro δ hδ
  obtain ⟨Y,hY⟩ := eventually_atTop.mp
    (hc.eventually_lt_const (show 0 < δ/2 by positivity))
  refine ⟨Y, fun p hp hpY => ?_⟩
  filter_upwards [h p hp (δ/2) (by positivity)] with A hA
  have hh : (c p+δ/2)*(A:ℝ) ≤ δ*A :=
    mul_le_mul_of_nonneg_right (by linarith [hY p hpY]) (Nat.cast_nonneg A)
  exact ⟨hA.1.trans hh,hA.2.trans hh⟩

end Erdos371AsymptoticSlopeAllowance

#print axioms Erdos371AsymptoticSlopeAllowance.density_half_of_eventual_slope_allowance
#print axioms Erdos371AsymptoticSlopeAllowance.density_half_of_asymptotic_slope_allowance
