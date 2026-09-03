import Submission.MultiplicativeChirpObstruction

/-!
A limitation of the moving chirp obstruction: it cannot have approximate
invariance under every multiplier up to the square root of its parameter.
This does not prove a correlation theorem for smooth-number indicators.
-/

namespace Erdos371.MultiplicativeChirpObstruction

open Filter
open scoped Topology

private lemma norm_mul_sub_one_le (z w : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖z * w - 1‖ ≤ ‖z - 1‖ + ‖w - 1‖ := by
  calc
    _ = ‖(z - 1) + z * (w - 1)‖ := by congr 1; ring
    _ ≤ ‖z - 1‖ + ‖z * (w - 1)‖ := norm_add_le _ _
    _ ≤ _ := by rw [norm_mul]; gcongr; exact mul_le_of_le_one_left (norm_nonneg _) hz

private lemma chirp_mul_distance_bound (t : ℝ) (a b : ℕ) :
    ‖chirp t (a * b) - 1‖ ≤ ‖chirp t a - 1‖ + ‖chirp t b - 1‖ := by
  rw [map_mul]
  exact norm_mul_sub_one_le _ _ (chirp_norm_le_one t a)

private lemma chirp_correlation_im_bound (t : ℝ) (n : ℕ) :
    (chirp t (n + 1) * (starRingEnd ℂ) (chirp t n)).im ≤
      ‖chirp t (n + 1) - 1‖ + ‖chirp t n - 1‖ := by
  calc
    _ = (chirp t (n + 1) * (starRingEnd ℂ) (chirp t n) - 1).im := by simp
    _ ≤ ‖chirp t (n + 1) * (starRingEnd ℂ) (chirp t n) - 1‖ :=
      Complex.im_le_norm _
    _ ≤ ‖chirp t (n + 1) - 1‖ + ‖(starRingEnd ℂ) (chirp t n) - 1‖ :=
      norm_mul_sub_one_le _ _ (chirp_norm_le_one t (n + 1))
    _ = _ := by
      rw [← map_one (starRingEnd ℂ), ← map_sub, Complex.norm_conj]
      simp only [map_one]

/-- Among three consecutive multipliers at the square-root scale, one chirp
value stays a definite distance from one. The estimate is uniform in N. -/
theorem chirp_sqrt_multiplier_separation (N : ℕ) (hN : 9 ≤ N) :
    ∃ k : ℕ, N.sqrt - 1 ≤ k ∧ k ≤ N.sqrt + 1 ∧
      (1 / 8 : ℝ) ≤ ‖chirp N k - 1‖ := by
  have hs : 3 ≤ N.sqrt := Nat.le_sqrt.mpr (by omega)
  let a := N.sqrt - 1
  have ha : 2 ≤ a := by dsimp [a]; omega
  have hs' : N.sqrt = a + 1 := by dsimp [a]; omega
  have hlow : (a + 1) * (a + 1) ≤ N := by simpa only [hs'] using Nat.sqrt_le N
  have hupp : N < (a + 2) * (a + 2) := by
    simpa only [hs', Nat.succ_eq_add_one, Nat.add_assoc] using Nat.lt_succ_sqrt N
  have hmid : N / 2 < a * (a + 2) := by
    have haux : (a + 2) * (a + 2) ≤ 2 * (a * (a + 2)) := by nlinarith
    omega
  have hle : a * (a + 2) ≤ N := by nlinarith
  have hpos : 0 < a * (a + 2) := by positivity
  have hl := increment_sine_high N (a * (a + 2)) hN hle hmid
  unfold incrementPhase at hl
  rw [← chirp_correlation_im N (a * (a + 2)) hpos] at hl
  have hu := chirp_correlation_im_bound (N : ℝ) (a * (a + 2))
  have he : a * (a + 2) + 1 = (a + 1) * (a + 1) := by ring
  rw [he] at hl hu
  have h1 := chirp_mul_distance_bound (N : ℝ) (a + 1) (a + 1)
  have h2 := chirp_mul_distance_bound (N : ℝ) a (a + 2)
  by_cases h : (1 / 8 : ℝ) ≤ ‖chirp N a - 1‖
  · exact ⟨a, le_rfl, by omega, h⟩
  by_cases h' : (1 / 8 : ℝ) ≤ ‖chirp N (a + 1) - 1‖
  · exact ⟨a + 1, by dsimp [a]; omega, by omega, h'⟩
  refine ⟨a + 2, by dsimp [a]; omega, by omega, ?_⟩
  linarith

/-- The fixed-multiplier convergence proved for a subsequence of chirps
cannot be upgraded to uniform convergence on this growing range. -/
theorem no_uniform_sqrt_multiplier_invariance (a : ℕ → ℕ)
    (ha : Tendsto a atTop atTop) :
    ¬ (∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
      ∀ k : ℕ, 0 < k → k ≤ (a j).sqrt + 1 → ‖chirp (a j) k - 1‖ < ε) := by
  intro h
  obtain ⟨j, hj, hsmall⟩ := ((ha.eventually_ge_atTop 9).and (h (1 / 8) (by norm_num))).exists
  obtain ⟨k, hklo, hkhi, hk⟩ := chirp_sqrt_multiplier_separation (a j) hj
  have hs : 3 ≤ (a j).sqrt := Nat.le_sqrt.mpr (by omega)
  exact hk.not_gt (hsmall k (by omega) hkhi)

/-- In contrast, the largest-prime cutoff is exactly unchanged by every
positive multiplier at most the cutoff, uniformly in the starting integer. -/
theorem maxPrimeFac_cutoff_small_multiplier (B k n : ℕ)
    (hk : 0 < k) (hkB : k ≤ B) :
    (Nat.maxPrimeFac (k * n) ≤ B ↔ Nat.maxPrimeFac n ≤ B) := by
  by_cases hn : n = 0
  · subst n; simp
  rw [Nat.maxPrimeFac_mul hk.ne' hn, max_le_iff]
  exact and_iff_right (Nat.maxPrimeFac_le.trans hkB)

#print axioms chirp_sqrt_multiplier_separation
#print axioms no_uniform_sqrt_multiplier_invariance
#print axioms maxPrimeFac_cutoff_small_multiplier

end Erdos371.MultiplicativeChirpObstruction
