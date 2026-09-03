import Submission.ClippedModulusExplore

/-! Cardinality tuning of clipped finite cyclic palettes. -/
namespace Erdos66ClippedModulusTuning
open Erdos66ClippedModulus Erdos66OuterMixedPrefix Erdos66SaturatingCyclicFamily
open scoped Classical
set_option maxHeartbeats 2000000

variable (M L : ℕ) [NeZero M] [NeZero L]

lemma clipped_quantized_prefix_error (hML : M ≤ L) (hLM : L ≤ 2*M)
    (C : Finset (ZMod L)) (w ε η : ℝ) (hw : 0 ≤ w)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hη : 0 ≤ η)
    (hprefix : ∀ z u, u ≤ L →
      |(prefixCount L C C z u:ℝ)-(u:ℝ)/L*actualMean L C C| ≤ η*actualMean L C C)
    (hmain : w ≤ (M:ℝ)/L*actualMean L C C ∧
      (M:ℝ)/L*actualMean L C C ≤ (1+ε)^2*w)
    (z : ZMod M) (u : ℕ) (hu : u ≤ M) :
    |(prefixCount M (rebase M L C) (rebase M L C) z u:ℝ)-(u:ℝ)/M*w| ≤
      (32*η+3*ε)*w := by
  let μ := actualMean L C C
  have hμ : 0 ≤ μ := actualMean_nonneg L C C
  have hm : (0:ℝ)<M := by exact_mod_cast NeZero.pos M
  have hl : (0:ℝ)<L := by exact_mod_cast NeZero.pos L
  have hhalf : (1:ℝ)/2 ≤ (M:ℝ)/L := by
    apply (le_div_iff₀ hl).mpr
    have hh : (L:ℝ) ≤ 2*M := by exact_mod_cast hLM
    linarith
  have hε2 : (1+ε)^2 ≤ 4 := by nlinarith
  have hε3 : (1+ε)^2-1 ≤ 3*ε := by nlinarith
  have hμ8 : μ ≤ 8*w := by
    have hh₁ := mul_le_mul_of_nonneg_right hhalf hμ
    have hh₂ := mul_le_mul_of_nonneg_right hε2 hw
    nlinarith only [hh₁,hh₂,hmain.2]
  have hdiff : 0 ≤ (M:ℝ)/L*μ-w ∧ (M:ℝ)/L*μ-w ≤ 3*ε*w := by
    have hh := mul_le_mul_of_nonneg_right hε3 hw
    constructor <;> nlinarith only [hmain.1,hmain.2,hh]
  have hu0 : (0:ℝ) ≤ (u:ℝ)/M := by positivity
  have hu1 : (u:ℝ)/M ≤ 1 := (div_le_one hm).mpr (by exact_mod_cast hu)
  have hcost : |(u:ℝ)/L*μ-(u:ℝ)/M*w| ≤ 3*ε*w := by
    have he : (u:ℝ)/L*μ-(u:ℝ)/M*w=(u:ℝ)/M*((M:ℝ)/L*μ-w) := by field_simp
    rw [he,abs_of_nonneg (mul_nonneg hu0 hdiff.1)]
    exact (mul_le_mul_of_nonneg_left hdiff.2 hu0).trans
      (by nlinarith only [mul_le_mul_of_nonneg_right hu1 (show 0 ≤ 3*ε*w by positivity)])
  have hp := rebase_prefix_error M L hML C C η hprefix z u hu
  have htri := abs_sub_le
    (prefixCount M (rebase M L C) (rebase M L C) z u:ℝ) ((u:ℝ)/L*μ) ((u:ℝ)/M*w)
  have hfinal := mul_le_mul_of_nonneg_left hμ8 hη
  nlinarith only [hp,htri,hcost,hfinal]

/-- Any specified positive clipped mean that lies in the palette's cardinality
range can be tuned, uniformly over all new cyclic targets and endpoint prefixes. -/
theorem exists_clipped_tuned_member (hML : M ≤ L) (hLM : L ≤ 2*M)
    (B : Finset (ZMod L)) (P : Finset (Finset (ZMod L)))
    (w ε η : ℝ) (hw : 0<w) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hη : 0 ≤ η)
    (hprefix : ∀ C∈P, ∀ z u, u ≤ L →
      |(prefixCount L C C z u:ℝ)-(u:ℝ)/L*actualMean L C C| ≤ η*actualMean L C C)
    (hcover : ∀ x : ℝ, (B.card:ℝ) ≤ x → x ≤ L →
      ∃ C∈P, x ≤ (C.card:ℝ) ∧ (C.card:ℝ) ≤ (1+ε)*x)
    (hbase : actualMean L B B ≤ w*L/M) (hcap : w ≤ M) :
    ∃ C∈P, ∀ z : ZMod M, ∀ u : ℕ, u ≤ M →
      |(prefixCount M (rebase M L C) (rebase M L C) z u:ℝ)-(u:ℝ)/M*w| ≤
        (32*η+3*ε)*w := by
  have hm : (0:ℝ)<M := by exact_mod_cast NeZero.pos M
  have hl : (0:ℝ)<L := by exact_mod_cast NeZero.pos L
  let x := Real.sqrt (w*(L:ℝ)^2/M)
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x^2=w*(L:ℝ)^2/M := Real.sq_sqrt (by positivity)
  have hxB : (B.card:ℝ) ≤ x := by
    have hb : (B.card:ℝ)^2 ≤ (w*L/M)*L := by
      have hh := (div_le_iff₀ hl).mp hbase
      nlinarith only [hh]
    apply le_of_sq_le_sq _ hx
    rw [hx2]
    convert hb using 1 <;> ring
  have hxL : x ≤ L := by
    apply le_of_sq_le_sq _ hl.le
    rw [hx2]
    apply (div_le_iff₀ hm).mpr
    have hh := mul_le_mul_of_nonneg_right hcap (sq_nonneg (L:ℝ))
    nlinarith only [hh]
  obtain ⟨C,hCP,hClo,hChi⟩ := hcover x hxB hxL
  have hC0 : (0:ℝ) ≤ C.card := Nat.cast_nonneg _
  have hslo : x^2 ≤ (C.card:ℝ)^2 := (sq_le_sq₀ hx hC0).mpr hClo
  have hshi : (C.card:ℝ)^2 ≤ (1+ε)^2*x^2 := by
    have hh := (sq_le_sq₀ hC0 (mul_nonneg (by linarith) hx)).mpr hChi
    nlinarith only [hh]
  have hmain : w ≤ (M:ℝ)/L*actualMean L C C ∧
      (M:ℝ)/L*actualMean L C C ≤ (1+ε)^2*w := by
    have ha : (0:ℝ) ≤ (M:ℝ)/(L:ℝ)^2 := by positivity
    have h₁ := mul_le_mul_of_nonneg_left hslo ha
    have h₂ := mul_le_mul_of_nonneg_left hshi ha
    have he : (M:ℝ)/(L:ℝ)^2*x^2=w := by rw [hx2]; field_simp
    have hμ : (M:ℝ)/(L:ℝ)^2*(C.card:ℝ)^2=(M:ℝ)/L*actualMean L C C := by
      dsimp only [actualMean]
      ring
    rw [he,hμ] at h₁
    have he' : (M:ℝ)/(L:ℝ)^2*((1+ε)^2*x^2)=(1+ε)^2*w := by rw [←he]; ring
    rw [hμ,he'] at h₂
    exact ⟨h₁,h₂⟩
  exact ⟨C,hCP,fun z u hu ↦ clipped_quantized_prefix_error M L hML hLM C w ε η
    hw.le hε hε1 hη (hprefix C hCP) hmain z u hu⟩

end Erdos66ClippedModulusTuning
