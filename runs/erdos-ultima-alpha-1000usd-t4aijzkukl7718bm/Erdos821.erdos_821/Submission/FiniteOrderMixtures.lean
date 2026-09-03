import Submission.CofinalMomentCriterion
import Submission.SymmetricDivisorHyperbola

/-!
# Finite mixtures of shifted-prime moment orders

A finite nonnegative mixture at arbitrarily large scales yields a single
order at arbitrarily large scales. The coefficients may vary with the scale,
but the finite support must be fixed first. The resulting criterion remains
unproved for actual shifted primes.

The final lemmas compare numerical coefficients only: mixing the currently
truncated coefficients cannot remove their geometric loss.
-/

open Nat Filter
open scoped Classical BigOperators Topology
namespace Erdos821.HigherDivisors
set_option maxHeartbeats 2000000

lemma exists_component_le_of_weighted_sum_le {ι : Type*} (K : Finset ι)
    (w a b : ι → ℝ) (hw : ∀ k ∈ K, 0 ≤ w k)
    (hpos : ∃ k ∈ K, 0 < w k)
    (hsum : (∑ k ∈ K, w k*a k) ≤ ∑ k ∈ K, w k*b k) :
    ∃ k ∈ K, a k ≤ b k := by
  by_contra hn
  push_neg at hn
  obtain ⟨j, hj, hwj⟩ := hpos
  have hlt : (∑ k ∈ K, w k*b k) < ∑ k ∈ K, w k*a k := by
    apply Finset.sum_lt_sum
    · intro k hk
      exact mul_le_mul_of_nonneg_left (hn k hk).le (hw k hk)
    · exact ⟨j, hj, mul_lt_mul_of_pos_left (hn j hj) hwj⟩
  exact hlt.not_ge hsum

/-- Fixed finite support, with arbitrary nonnegative scale-dependent weights.
No lower bound of this strength is asserted here. -/
def FiniteMixtureMomentLower : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ t : ℕ, 2 ≤ t → ∀ B : ℕ,
    ∃ K : Finset ℕ, (∀ k ∈ K, B ≤ k ∧ 2 ≤ k) ∧
      ∀ M : ℕ, ∃ L : ℕ, M ≤ L ∧ ∃ w : ℕ → ℝ,
        (∀ k ∈ K, 0 ≤ w k) ∧ (∃ k ∈ K, 0 < w k) ∧
        (∑ k ∈ K, w k *
          (θ^k*(momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(k.factorial : ℝ))) ≤
        ∑ k ∈ K, w k*shiftedPrimeMoment k (momentScaleX t L)

lemma cofinal_geometric_moments_of_finite_mixture (H : FiniteMixtureMomentLower) :
    CofinalGeometricMomentLower := by
  intro θ hθ0 hθ1 t ht B
  obtain ⟨K, hK, hscales⟩ := H θ hθ0 hθ1 t ht B
  have hf : ∃ᶠ L : ℕ in atTop, ∃ k ∈ K,
      θ^k*(momentScaleX t L : ℝ)*(Real.log (momentScaleX t L))^(k-2)/(k.factorial : ℝ) ≤
        shiftedPrimeMoment k (momentScaleX t L) := by
    rw [frequently_atTop]
    intro M
    obtain ⟨L, hL, w, hw, hpos, hsum⟩ := hscales M
    exact ⟨L, hL, exists_component_le_of_weighted_sum_le K w _ _ hw hpos hsum⟩
  obtain ⟨k, hk, hfreq⟩ := K.frequently_exists.mp hf
  exact ⟨k, (hK k hk).1, (hK k hk).2, frequently_atTop.mp hfreq⟩

lemma finite_mixture_of_cofinal_geometric_moments (H : CofinalGeometricMomentLower) :
    FiniteMixtureMomentLower := by
  intro θ hθ0 hθ1 t ht B
  obtain ⟨k, hkB, hk2, hscales⟩ := H θ hθ0 hθ1 t ht B
  refine ⟨{k}, ?_, ?_⟩
  · intro j hj
    have he : j=k := Finset.mem_singleton.mp hj
    subst j
    exact ⟨hkB, hk2⟩
  · intro M
    obtain ⟨L, hL, hmoment⟩ := hscales M
    refine ⟨L, hL, fun _ => 1, ?_, ?_, ?_⟩
    · intro j hj
      norm_num
    · exact ⟨k, Finset.mem_singleton_self _, by norm_num⟩
    · simpa only [Finset.sum_singleton, one_mul] using hmoment

/-- Finite mixtures do not weaken the previously isolated arithmetic input. -/
theorem finite_mixture_iff_cofinal_geometric :
    FiniteMixtureMomentLower ↔ CofinalGeometricMomentLower :=
  ⟨cofinal_geometric_moments_of_finite_mixture, finite_mixture_of_cofinal_geometric_moments⟩

/-- Conditional only: no mixture lower estimate for primes has been supplied. -/
theorem erdos_821_of_finite_order_mixtures (H : FiniteMixtureMomentLower) :
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  erdos_821_of_cofinal_geometric_moments (cofinal_geometric_moments_of_finite_mixture H)

lemma eventually_truncated_coefficient_lt_geometric (θ ρ c : ℝ)
    (hθ : 0 ≤ θ) (hρ : 0 < ρ) (hθρ : θ < ρ) (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, (k+1 : ℝ)*θ^k/(k.factorial : ℝ) <
      c*(ρ^k/((k+1).factorial : ℝ)) := by
  have hq : 0 ≤ θ/ρ := div_nonneg hθ hρ.le
  have hq1 : θ/ρ < 1 := (div_lt_one hρ).mpr hθρ
  filter_upwards [eventually_symmetrized_coefficient_lt_factorial (θ/ρ) c hq hq1 hc] with k hk
  have hpow : 0 < ρ^k := pow_pos hρ _
  have h := mul_lt_mul_of_pos_right hk hpow
  have he : ((k+1 : ℝ)*(θ/ρ)^k/(k.factorial : ℝ))*ρ^k =
      (k+1 : ℝ)*θ^k/(k.factorial : ℝ) := by
    rw [div_pow]
    field_simp
  rw [he] at h
  convert h using 1
  ring

/-- Uniform over all finite supports above B, and all nonnegative weights.
This is a comparison of proposed main coefficients, not a prime estimate. -/
theorem exists_cutoff_all_finite_mixtures_small (θ ρ c : ℝ)
    (hθ : 0 ≤ θ) (hρ : 0 < ρ) (hθρ : θ < ρ) (hc : 0 < c) :
    ∃ B : ℕ, ∀ K : Finset ℕ, (∀ k ∈ K, B ≤ k) →
      ∀ w : ℕ → ℝ, (∀ k ∈ K, 0 ≤ w k) →
      (∑ k ∈ K, w k*((k+1 : ℝ)*θ^k/(k.factorial : ℝ))) ≤
        c*∑ k ∈ K, w k*(ρ^k/((k+1).factorial : ℝ)) := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    (eventually_truncated_coefficient_lt_geometric θ ρ c hθ hρ hθρ hc)
  refine ⟨B, ?_⟩
  intro K hK w hw
  calc
    _ ≤ ∑ k ∈ K, w k*(c*(ρ^k/((k+1).factorial : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hB k (hK k hk)).le (hw k hk)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

end Erdos821.HigherDivisors
