import Submission.StepConvolutionBridgeExplore
import Submission.MonotoneIntervalFibersExplore

/-! A fixed finite height grid quantizes every bounded monotone profile,
independently of the number of its changes. -/
namespace Erdos66BoundedProfileQuantization
open Erdos66StepConvolutionBridge
open scoped Classical
set_option maxHeartbeats 2200000

lemma normConv_bounds (M : ℕ) [NeZero M] (f : ℕ → ℝ) (W : ℝ)
    (hW : 0 ≤ W) (hf : ∀ x<M, 0 ≤ f x ∧ f x ≤ W) (n : ℕ) :
    0 ≤ normConv M f n ∧ normConv M f n ≤ W^2 := by
  have hM : (0:ℝ)<M := by exact_mod_cast NeZero.pos M
  constructor
  · apply div_nonneg _ hM.le
    apply Finset.sum_nonneg
    intro x hx
    split_ifs with hn
    · exact mul_nonneg (hf x (Finset.mem_range.mp hx)).1 (hf (n-x) hn.2).1
    · exact le_rfl
  · apply (div_le_iff₀ hM).mpr
    calc
      _ ≤ ∑ _x∈Finset.range M, W^2 := by
        apply Finset.sum_le_sum
        intro x hx
        split_ifs with hn
        · have hh := mul_le_mul (hf x (Finset.mem_range.mp hx)).2 (hf (n-x) hn.2).2
            (hf (n-x) hn.2).1 hW
          simpa only [pow_two] using hh
        · exact sq_nonneg _
      _ = _ := by simp [mul_comm]

lemma normConv_bracket (M : ℕ) [NeZero M] (f g : ℕ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hf : ∀ x<M, 0 ≤ f x ∧ f x ≤ g x ∧ g x ≤ R*f x) (n : ℕ) :
    normConv M f n ≤ normConv M g n ∧ normConv M g n ≤ R^2*normConv M f n := by
  constructor
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
    apply Finset.sum_le_sum
    intro x hx
    split_ifs with hn
    · have hhx := hf x (Finset.mem_range.mp hx)
      have hhy := hf (n-x) hn.2
      exact mul_le_mul hhx.2.1 hhy.2.1 hhy.1 (hhx.1.trans hhx.2.1)
    · exact le_rfl
  · unfold normConv
    rw [←mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    split_ifs with hn
    · have hhx := hf x (Finset.mem_range.mp hx)
      have hhy := hf (n-x) hn.2
      have hh := mul_le_mul hhx.2.2 hhy.2.2 (hhy.1.trans hhy.2.1) (mul_nonneg hR hhx.1)
      nlinarith only [hh]
    · simp only [mul_zero,le_refl]

lemma normConv_quantization_error (M : ℕ) [NeZero M] (f g : ℕ → ℝ) (W R : ℝ)
    (hW : 0 ≤ W) (hR : 1 ≤ R)
    (hf : ∀ x<M, 0 ≤ f x ∧ f x ≤ W ∧ f x ≤ g x ∧ g x ≤ R*f x) (n : ℕ) :
    |normConv M g n-normConv M f n| ≤ (R^2-1)*W^2 := by
  have hR0 : 0 ≤ R := by linarith
  obtain ⟨hl,hu⟩ := normConv_bracket M f g R hR0 (fun x hx ↦ ⟨(hf x hx).1,(hf x hx).2.2⟩) n
  obtain ⟨h0,hW'⟩ := normConv_bounds M f W hW (fun x hx ↦ ⟨(hf x hx).1,(hf x hx).2.1⟩) n
  have hR2 : 0 ≤ R^2-1 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hW' hR2
  rw [abs_of_nonneg (sub_nonneg.mpr hl)]
  nlinarith only [hu,hh]

noncomputable def binIndex (e : ℝ) (J : ℕ) (x : ℝ) : Fin (J+1) :=
  ⟨min J ⌈(x-1)/e⌉₊,Nat.lt_succ_of_le (min_le_left _ _)⟩

noncomputable def gridWeight (e : ℝ) {J : ℕ} (j : Fin (J+1)) : ℝ := 1+e*j.val

lemma binIndex_mono (e : ℝ) (he : 0<e) (J : ℕ) : Monotone (binIndex e J) := by
  intro x y hxy
  apply Fin.le_iff_val_le_val.mpr
  exact min_le_min_left J (Nat.ceil_mono (div_le_div_of_nonneg_right (by linarith : x-1 ≤ y-1) he.le))

lemma gridWeight_ge_one (e : ℝ) (he : 0 ≤ e) {J : ℕ} (j : Fin (J+1)) : 1 ≤ gridWeight e j := by
  dsimp [gridWeight]
  have hh := mul_nonneg he (Nat.cast_nonneg j.val)
  linarith

lemma bin_weight_bracket (e W x : ℝ) (he : 0<e) (hx1 : 1 ≤ x) (hxW : x ≤ W) :
    x ≤ gridWeight e (binIndex e ⌈(W-1)/e⌉₊ x) ∧
      gridWeight e (binIndex e ⌈(W-1)/e⌉₊ x) ≤ (1+e)*x := by
  have hidx : ⌈(x-1)/e⌉₊ ≤ ⌈(W-1)/e⌉₊ :=
    Nat.ceil_mono (div_le_div_of_nonneg_right (by linarith) he.le)
  simp only [gridWeight,binIndex,min_eq_right hidx]
  have hl := (div_le_iff₀ he).mp (Nat.le_ceil ((x-1)/e))
  have hu := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg (by linarith : 0 ≤ x-1) he.le)) he
  have hcancel : ((x-1)/e+1)*e=x-1+e := by field_simp
  rw [hcancel] at hu
  have hm := mul_nonneg he.le (sub_nonneg.mpr hx1)
  constructor <;> nlinarith only [hl,hu,hm]

end Erdos66BoundedProfileQuantization
