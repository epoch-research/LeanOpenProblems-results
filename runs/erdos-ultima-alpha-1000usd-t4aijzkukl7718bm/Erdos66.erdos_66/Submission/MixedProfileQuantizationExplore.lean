import Submission.MixedStepBridgeExplore
import Submission.BoundedProfileQuantizationExplore

/-! Multiplicative quantization errors for two independently chosen profiles. -/
namespace Erdos66MixedProfileQuantization
open Erdos66MixedStepBridge
open scoped Classical
set_option maxHeartbeats 2200000

lemma normMixedConv_bounds (M : ℕ) [NeZero M] (f g : ℕ → ℝ) (W : ℝ)
    (hW : 0 ≤ W) (hf : ∀ x<M, 0 ≤ f x ∧ f x ≤ W)
    (hg : ∀ x<M, 0 ≤ g x ∧ g x ≤ W) (n : ℕ) :
    0 ≤ normMixedConv M f g n ∧ normMixedConv M f g n ≤ W^2 := by
  have hM : (0:ℝ)<M := by exact_mod_cast NeZero.pos M
  constructor
  · apply div_nonneg _ hM.le
    apply Finset.sum_nonneg
    intro x hx
    split_ifs with hn
    · exact mul_nonneg (hf x (Finset.mem_range.mp hx)).1 (hg (n-x) hn.2).1
    · exact le_rfl
  · apply (div_le_iff₀ hM).mpr
    calc
      _ ≤ ∑ _x∈Finset.range M, W^2 := by
        apply Finset.sum_le_sum
        intro x hx
        split_ifs with hn
        · have hh := mul_le_mul (hf x (Finset.mem_range.mp hx)).2 (hg (n-x) hn.2).2
            (hg (n-x) hn.2).1 hW
          simpa only [pow_two] using hh
        · exact sq_nonneg _
      _ = _ := by simp [mul_comm]

lemma normMixedConv_bracket (M : ℕ) [NeZero M] (f g F G : ℕ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hf : ∀ x<M, 0 ≤ f x ∧ f x ≤ F x ∧ F x ≤ R*f x)
    (hg : ∀ x<M, 0 ≤ g x ∧ g x ≤ G x ∧ G x ≤ R*g x) (n : ℕ) :
    normMixedConv M f g n ≤ normMixedConv M F G n ∧
      normMixedConv M F G n ≤ R^2*normMixedConv M f g n := by
  constructor
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
    apply Finset.sum_le_sum
    intro x hx
    split_ifs with hn
    · have hhx := hf x (Finset.mem_range.mp hx)
      have hhy := hg (n-x) hn.2
      exact mul_le_mul hhx.2.1 hhy.2.1 hhy.1 (hhx.1.trans hhx.2.1)
    · exact le_rfl
  · unfold normMixedConv
    rw [←mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    split_ifs with hn
    · have hhx := hf x (Finset.mem_range.mp hx)
      have hhy := hg (n-x) hn.2
      have hh := mul_le_mul hhx.2.2 hhy.2.2 (hhy.1.trans hhy.2.1) (mul_nonneg hR hhx.1)
      nlinarith only [hh]
    · simp only [mul_zero,le_refl]

lemma normMixedConv_quantization_error (M : ℕ) [NeZero M] (f g F G : ℕ → ℝ) (W R : ℝ)
    (hW : 0 ≤ W) (hR : 1 ≤ R)
    (hf : ∀ x<M, 0 ≤ f x ∧ f x ≤ W ∧ f x ≤ F x ∧ F x ≤ R*f x)
    (hg : ∀ x<M, 0 ≤ g x ∧ g x ≤ W ∧ g x ≤ G x ∧ G x ≤ R*g x) (n : ℕ) :
    |normMixedConv M F G n-normMixedConv M f g n| ≤ (R^2-1)*W^2 := by
  have hR0 : 0 ≤ R := by linarith
  obtain ⟨hl,hu⟩ := normMixedConv_bracket M f g F G R hR0
    (fun x hx ↦ ⟨(hf x hx).1,(hf x hx).2.2⟩) (fun x hx ↦ ⟨(hg x hx).1,(hg x hx).2.2⟩) n
  obtain ⟨h0,hW'⟩ := normMixedConv_bounds M f g W hW
    (fun x hx ↦ ⟨(hf x hx).1,(hf x hx).2.1⟩) (fun x hx ↦ ⟨(hg x hx).1,(hg x hx).2.1⟩) n
  have hR2 : 0 ≤ R^2-1 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hW' hR2
  rw [abs_of_nonneg (sub_nonneg.mpr hl)]
  nlinarith only [hu,hh]

end Erdos66MixedProfileQuantization
