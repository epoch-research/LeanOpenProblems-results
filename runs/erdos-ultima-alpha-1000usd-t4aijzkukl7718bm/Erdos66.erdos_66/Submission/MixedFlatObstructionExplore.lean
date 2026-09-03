import Submission.RelativeCyclicFamilyExplore
import Submission.CyclicVarianceExplore

/-! Flat self-convolution does not imply flat mixed convolution, even for
arbitrarily accurate finite cyclic examples. This is not a disproof of Erdos 66. -/
namespace Erdos66MixedFlatObstruction
open Erdos66RelativeCyclicFamily Erdos66CyclicVariance Erdos66MixedEnergy
open scoped Classical
set_option maxHeartbeats 800000

section Group
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma mem_image_neg (B : Finset G) (x : G) : x ∈ B.image Neg.neg ↔ -x ∈ B := by
  constructor
  · rintro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    simpa only [neg_neg] using ha
  · intro hx
    exact Finset.mem_image.mpr ⟨-x, hx, neg_neg x⟩

lemma reflected_self_count (B : Finset G) (z : G) :
    ((B.image Neg.neg).filter (fun a ↦ z - a ∈ B.image Neg.neg)).card =
      (B.filter (fun a ↦ -z - a ∈ B)).card := by
  apply Finset.card_bij (fun a ha ↦ -a)
  · intro a ha
    obtain ⟨ha, hb⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨(mem_image_neg B a).mp ha, by
      have hh := (mem_image_neg B (z - a)).mp hb
      convert hh using 1 <;> abel⟩
  · intro a ha b hb he
    exact neg_injective he
  · intro a ha
    obtain ⟨ha, hb⟩ := Finset.mem_filter.mp ha
    refine ⟨-a, Finset.mem_filter.mpr ⟨?_, ?_⟩, neg_neg a⟩
    · exact (mem_image_neg B (-a)).mpr (by simpa only [neg_neg] using ha)
    · apply (mem_image_neg B (z - -a)).mpr
      convert hb using 1 <;> abel

lemma reflected_mixed_zero (B : Finset G) :
    (B.filter (fun a ↦ (0 : G) - a ∈ B.image Neg.neg)).card = B.card := by
  have he : B.filter (fun a ↦ (0 : G) - a ∈ B.image Neg.neg) = B := by
    ext a
    simp only [Finset.mem_filter, zero_sub, mem_image_neg, neg_neg, and_self]
  rw [he]

lemma self_count_mass (B : Finset G) :
    (∑ z : G, ((B.filter (fun a ↦ z - a ∈ B)).card : ℝ)) = (B.card : ℝ) ^ 2 := by
  have hc (z : G) : conv (indicator B) (indicator B) z =
      ((B.filter (fun a ↦ z - a ∈ B)).card : ℝ) := by
    simp [conv, indicator, ← Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  simp_rw [← hc]
  rw [sum_conv, sum_indicator, pow_two]

lemma card_sq_lower (B : Finset G) (β η : ℝ)
    (hB : ∀ z : G, |(((B.filter (fun a ↦ z - a ∈ B)).card : ℝ) - β)| ≤ η * β) :
    (Fintype.card G : ℝ) * ((1 - η) * β) ≤ (B.card : ℝ) ^ 2 := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun z _ ↦
    show (1 - η) * β ≤ ((B.filter (fun a ↦ z - a ∈ B)).card : ℝ) by
      have hz := (abs_le.mp (hB z)).1
      nlinarith)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, self_count_mass] using hh

end Group

/-- The center β is independent of the arbitrarily large mixed peak. -/
theorem exists_unbounded_mixed_peak (η : ℝ) (hη : 0 < η) :
    ∃ β : ℝ, 0 < β ∧ ∀ R : ℝ, 0 < R →
      ∃ M : ℕ, ∃ hM : NeZero M, ∃ B C : Finset (ZMod M),
        (∀ z : ZMod M, |(((B.filter (fun a ↦ z - a ∈ B)).card : ℝ) - β)| ≤ η * β) ∧
        (∀ z : ZMod M, |(((C.filter (fun a ↦ z - a ∈ C)).card : ℝ) - β)| ≤ η * β) ∧
        R * β < ((B.filter (fun a ↦ (0 : ZMod M) - a ∈ C)).card : ℝ) := by
  let ρ : ℝ := min η (1 / 2)
  have hρ : 0 < ρ := lt_min hη (by norm_num)
  have hρη : ρ ≤ η := min_le_left _ _
  have hρ1 : ρ ≤ 1 / 2 := min_le_right _ _
  obtain ⟨β, hβ, hfamily⟩ := exists_relative_cyclic_family ρ hρ 1
  refine ⟨β, hβ, fun R hR ↦ ?_⟩
  have hpos : 0 < (1 - ρ) * β := mul_pos (by linarith) hβ
  obtain ⟨P, hP⟩ := exists_nat_gt ((R * β) ^ 2 / ((1 - ρ) * β))
  obtain ⟨M, hMP, hM, F, hF0, hFmono, hF⟩ := hfamily P
  letI := hM
  let B := F 1
  have hB (z : ZMod M) : |(((B.filter (fun a ↦ z - a ∈ B)).card : ℝ) - β)| ≤ ρ * β := by
    simpa only [B, Nat.cast_one, mul_one] using hF 1 le_rfl 1 le_rfl z
  have hBη (z : ZMod M) : |(((B.filter (fun a ↦ z - a ∈ B)).card : ℝ) - β)| ≤ η * β :=
    (hB z).trans (mul_le_mul_of_nonneg_right hρη hβ.le)
  refine ⟨M, hM, B, B.image Neg.neg, hBη, ?_, ?_⟩
  · intro z
    rw [reflected_self_count B z]
    exact hBη (-z)
  · rw [reflected_mixed_zero B]
    have hl := card_sq_lower B β ρ hB
    rw [ZMod.card] at hl
    have hM' : (R * β) ^ 2 / ((1 - ρ) * β) < (M : ℝ) :=
      hP.trans (by exact_mod_cast hMP)
    have hh := (div_lt_iff₀ hpos).mp hM'
    have hnonneg : 0 ≤ R * β := mul_nonneg hR.le hβ.le
    nlinarith [Nat.cast_nonneg (α := ℝ) B.card]

end Erdos66MixedFlatObstruction
