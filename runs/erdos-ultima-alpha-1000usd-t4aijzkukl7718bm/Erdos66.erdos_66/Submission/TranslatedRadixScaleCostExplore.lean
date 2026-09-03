import Submission.PatchedTranslatedRadixExplore

/-! Necessary scale costs for the entrywise-flat, all-translates radix lift.
These are restrictions on this construction, not on arbitrary witnesses. -/
namespace Erdos66TranslatedRadixScaleCost
open Erdos66OriginRepair Erdos66PatchedTranslatedRadix
open scoped Classical
set_option maxHeartbeats 1200000

lemma integer_mean_lower (k : ℕ) (μ δ : ℝ) (hμ : 0 < μ) (hδ : δ ≤ 1/2)
    (hk : |(k : ℝ) - μ| ≤ δ * μ) : (2 : ℝ)/3 ≤ μ := by
  have hd := mul_le_mul_of_nonneg_right hδ hμ.le
  have hb := abs_le.mp hk
  have hkr : (0 : ℝ) < k := by linarith
  have hkn : 1 ≤ k := by exact_mod_cast hkr
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hkn
  linarith

variable (L M : ℕ) [NeZero L] [NeZero M]

lemma patchedRadix_count_lower (A : Finset (ZMod L)) (P : ZMod L → Finset (ZMod M))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j))) (μ δ : ℝ)
    (hμ : 0 < μ) (hδ : δ ≤ 1/2)
    (hb : ∀ i j z, |(pairCount (P i) (P j) z : ℝ) - μ| ≤ δ * μ)
    (z : ZMod (L*M)) :
    (L : ℝ) * (A.card : ℝ)^2 / 3 - 2 * L ≤
      (pairCount (patchedRadix L M A P) (patchedRadix L M A P) z : ℝ) := by
  have hm := integer_mean_lower _ μ δ hμ hδ (hb 0 0 0)
  have hd := mul_le_mul_of_nonneg_right hδ hμ.le
  have hD : 0 ≤ (L : ℝ) * (A.card : ℝ)^2 := by positivity
  have he := (abs_le.mp (patchedRadix_error L M A P hP μ δ hb z)).1
  have hh := mul_le_mul_of_nonneg_right hd hD
  have hh' := mul_le_mul_of_nonneg_right hm hD
  nlinarith

lemma cap_scale_cost (A : Finset (ZMod L)) (P : ZMod L → Finset (ZMod M))
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j))) (μ δ C : ℝ)
    (hμ : 0 < μ) (hδ : δ ≤ 1/2)
    (hb : ∀ i j z, |(pairCount (P i) (P j) z : ℝ) - μ| ≤ δ * μ)
    (z : ZMod (L*M))
    (hcap : (pairCount (patchedRadix L M A P) (patchedRadix L M A P) z : ℝ) ≤
      C * Real.log ((L*M : ℕ) : ℝ)) :
    (L : ℝ) * (A.card : ℝ)^2 ≤ 3*C*Real.log ((L*M : ℕ) : ℝ) + 6*L := by
  have hh := patchedRadix_count_lower L M A P hP μ δ hμ hδ hb z
  linarith

lemma cap_requires_exponential_scale (A : Finset (ZMod L))
    (P : ZMod L → Finset (ZMod M)) (hA : 3 ≤ A.card)
    (hP : Pairwise (fun i j ↦ Disjoint (P i) (P j))) (μ δ C : ℝ)
    (hμ : 0 < μ) (hδ : δ ≤ 1/2) (hC : 0 < C)
    (hb : ∀ i j z, |(pairCount (P i) (P j) z : ℝ) - μ| ≤ δ * μ)
    (z : ZMod (L*M))
    (hcap : (pairCount (patchedRadix L M A P) (patchedRadix L M A P) z : ℝ) ≤
      C * Real.log ((L*M : ℕ) : ℝ)) :
    Real.exp ((L : ℝ)/C) ≤ (L*M : ℕ) := by
  have he := cap_scale_cost L M A P hP μ δ C hμ hδ hb z hcap
  have hAr : (3 : ℝ) ≤ A.card := by exact_mod_cast hA
  have hLL : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left (show (9 : ℝ) ≤ (A.card : ℝ)^2 by nlinarith) hLL
  have hlog : (L : ℝ) ≤ C * Real.log ((L*M : ℕ) : ℝ) := by nlinarith
  have hprod : (0 : ℝ) < (L*M : ℕ) := by exact_mod_cast Nat.mul_pos (NeZero.pos L) (NeZero.pos M)
  rw [← Real.exp_log hprod]
  exact Real.exp_le_exp.mpr ((div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hlog))

end Erdos66TranslatedRadixScaleCost
