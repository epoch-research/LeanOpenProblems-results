import Submission.BuchstabLevelMonotonicity
import Submission.FirstHitIntegerCutoff

/-! A constant-factor enlarged divisor source. Its integer support dominates a
ceiling square-root cutoff without changing the divisor exponent. The factor
four in the error budget is retained explicitly. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg

noncomputable def scaledSelbergBase (p : ℕ → ℕ) (k : ℕ) (D : ℝ) : ℝ := selbergBase p k (4*D)
noncomputable def scaledSelbergCost (k : ℕ) (D : ℝ) : ℝ := selbergCost k (4*D)

lemma scaledSelbergCost_nonneg (k : ℕ) (D : ℝ) : 0 ≤ scaledSelbergCost k D := selbergCost_nonneg _ _

lemma scaledSelbergCost_le (k : ℕ) (D : ℝ) (hD : 1 ≤ D) : scaledSelbergCost k D ≤ 4*D :=
  selbergCost_le_level k (4*D) (by linarith)

lemma ceiling_sqrt_le_scaledCutoff (D : ℝ) (hD : 1 ≤ D) : ⌈sqrt D⌉₊ ≤ selbergCutoff (4*D) := by
  have hr : 1 ≤ sqrt D := by simpa using sqrt_le_sqrt hD
  have hs : sqrt (4*D) = 2*sqrt D := by rw [sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  have hc : (⌈sqrt D⌉₊ : ℝ) ≤ sqrt (4*D) := by
    rw [hs]
    have hh := Nat.ceil_lt_add_one (sqrt_nonneg D)
    linarith
  exact (Nat.le_floor hc).trans (le_max_right _ _)

lemma scaledSelbergBase_antitone (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (k : ℕ) :
    Antitone (scaledSelbergBase p k) :=
  fun _ _ hDE => selbergBase_antitone p hp k (mul_le_mul_of_nonneg_left hDE (by norm_num))

lemma scaledSelbergBase_density (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (k : ℕ) (D : ℝ) :
    prefixDensity (fun i => 1/(p i : ℝ)) k ≤ scaledSelbergBase p k D :=
  selbergBase_density p hp k (4*D)

lemma scaledSelbergBase_le_ceiling (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (k : ℕ) (D : ℝ) (hD : 1 ≤ D) :
    scaledSelbergBase p k D ≤ 1/normalizer (fun i : Fin k => 1/(p i.val : ℝ))
      (divisorSupport (fun i : Fin k => p i.val) ⌈sqrt D⌉₊) := by
  have hR : 0 < ⌈sqrt D⌉₊ := Nat.ceil_pos.mpr (sqrt_pos.mpr (by linarith))
  have hq (i : Fin k) : 0 < 1/(p i.val : ℝ) ∧ 1/(p i.val : ℝ) < 1 := by
    have hi : (1 : ℝ) < p i.val := by exact_mod_cast (hp i.val).one_lt
    exact ⟨by positivity, (div_lt_one (by linarith)).mpr hi⟩
  apply inverse_normalizer_antitone _ hq _ _ (divisorSupport_nonempty _ _ hR)
  intro T hT
  rw [mem_divisorSupport] at hT ⊢
  exact hT.trans (ceiling_sqrt_le_scaledCutoff D hD)

lemma scaled_refined_lowerError_le (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (hmono : StrictMono p) (a : ℝ) (ha : 1 < a) (n k : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    lowerErrorStep (fun i => 1/(p i : ℝ)) (primeKeep p)
      (upperError (fun i => 1/(p i : ℝ)) (primeKeep p) scaledSelbergCost n) k D ≤
        4*(1+reciprocalPowerConstant a)^(2*n+1)*D^a := by
  apply refined_lowerError_le_rpow _ _ _ a 4 _ (by linarith) (by norm_num)
    (reciprocalPowerConstant_nonneg a) (fun i => by positivity)
    (reciprocal_power_sum_le p hmono.injective a ha) (primeKeep_levels p hp hmono) _ n k D hD
  intro k D hD
  apply (scaledSelbergCost_le k D hD).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  simpa using rpow_le_rpow_of_exponent_le hD ha.le

/-- A fully charged survivor criterion for the enlarged canonical source. -/
theorem survivor_of_scaled_selberg_refinement {α : Type*} (A : Finset α) (w : α → ℝ)
    (ω : α → ℕ → Bool) (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime)
    (hmono : StrictMono p) (x D : ℝ) (K : ℕ) (hx : 0 ≤ x) (hD : 0 ≤ D)
    (hw : ∀ j ∈ A, 0 ≤ w j)
    (hmoment : ∀ T : Finset ℕ, T ⊆ range K →
      |moment A w ω T-x*∏ i ∈ T, 1/(p i : ℝ)| ≤ 1)
    (a : ℝ) (ha : 1 < a) (n : ℕ)
    (hpos : 4*(1+reciprocalPowerConstant a)^(2*n+1)*D^a <
      x*lowerStep (fun i => 1/(p i : ℝ)) (primeKeep p)
        (upperMain (fun i => 1/(p i : ℝ)) (primeKeep p) (scaledSelbergBase p) n) K D) :
    ∃ j ∈ A, ∀ i < K, ω j i = false := by
  apply survivor_of_refinement A w ω (fun i => 1/(p i : ℝ)) x D K (primeKeep p)
    (scaledSelbergBase p) scaledSelbergCost hw (fun i => by positivity) hx
      scaledSelbergCost_nonneg hmoment _ n
  · exact (scaled_refined_lowerError_le p hp hmono a ha n K D hD).trans_lt hpos
  · intro k hk T hTK hT
    simpa only [scaledSelbergBase, scaledSelbergCost, mul_assoc] using
      conditional_selberg_upper A w ω p hp hmono.injective x (4*D) K hw hmoment k hk T hTK hT

#print axioms scaledSelbergBase_le_ceiling
#print axioms survivor_of_scaled_selberg_refinement
end Erdos970.RecursiveSieve.Buchstab
