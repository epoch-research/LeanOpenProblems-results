import Submission.MaskedUniformityCounting
import Submission.FourierMultilinearTransfer

/-! Generalized von Neumann and counting bounds with an arbitrary weight on
the common difference. The cost is exactly the Fourier L1 mass of the weight;
no density-free localization principle is assumed. -/
namespace Erdos3StepWeightedCounting
open Finset Erdos3MaskedUniformityCounting Erdos3UniformityCounting
  Erdos3LinearFormsUniformity Erdos3FiniteUniformity Erdos3FiniteFourier
  Erdos3FourierMultilinearTransfer
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- A weighted average is controlled by its character tests and the Fourier
mass of its weight. -/
lemma weighted_expect_fourier_bound (w H : G → ℂ) {η : ℝ}
    (hH : ∀ χ : AddChar G ℂ, ‖𝔼 d : G, χ d*H d‖ ≤ η) :
    ‖𝔼 d : G, w d*H d‖ ≤ fourierMass w*η := by
  have he : (𝔼 d : G, w d*H d) =
      ∑ χ : AddChar G ℂ, hat w χ*(𝔼 d : G, χ d*H d) := by
    calc
      _ = 𝔼 d : G, ∑ χ : AddChar G ℂ, hat w χ*(χ d*H d) := by
        apply expect_congr rfl
        intro d _
        rw [inversion w d,sum_mul]
        apply sum_congr rfl
        intro χ _
        ring
      _ = _ := by rw [expect_sum_comm]; simp only [← mul_expect]
  rw [he]
  calc
    _ ≤ ∑ χ : AddChar G ℂ, ‖hat w χ*(𝔼 d : G, χ d*H d)‖ := norm_sum_le _ _
    _ ≤ ∑ χ : AddChar G ℂ, ‖hat w χ‖*η := by
      apply sum_le_sum
      intro χ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hH χ) (norm_nonneg _)
    _ = _ := (sum_mul ..).symm

variable {F : Type*} [Field F] [Fintype F]

noncomputable def weightedLinearAverage {k : ℕ} (v : Fin k → F)
    (f : Fin k → F → ℂ) (w : F → ℂ) : ℂ :=
  𝔼 d : F, w d*(𝔼 x : F, ∏ i : Fin k, f i (x+v i*d))

noncomputable def twoSlopePhase {k : ℕ} (v : Fin k → F) (j s : Fin k)
    (χ : AddChar F ℂ) (i : Fin k) (y : F) : ℂ :=
  (if i = j then χ (y/(v j-v s)) else 1)*
    (if i = s then χ (-y/(v j-v s)) else 1)

lemma twoSlopePhase_norm {k : ℕ} (v : Fin k → F) (j s : Fin k)
    (χ : AddChar F ℂ) (i : Fin k) (y : F) :
    ‖twoSlopePhase v j s χ i y‖ = 1 := by
  unfold twoSlopePhase
  rw [norm_mul]
  split_ifs <;> simp only [χ.norm_apply,norm_one,mul_one]

lemma twoSlopePhase_off {k : ℕ} (v : Fin k → F) (j s : Fin k)
    (χ : AddChar F ℂ) {i : Fin k} (hij : i ≠ j) (his : i ≠ s) (y : F) :
    twoSlopePhase v j s χ i y = 1 := by simp only [twoSlopePhase,if_neg hij,if_neg his,mul_one]

lemma twoSlopePhase_product {k : ℕ} (v : Fin k → F) {j s : Fin k}
    (hjs : v j ≠ v s) (χ : AddChar F ℂ) (x d : F) :
    (∏ i : Fin k, twoSlopePhase v j s χ i (x+v i*d)) = χ d := by
  simp only [twoSlopePhase,prod_mul_distrib,prod_ite_eq',mem_univ,if_true]
  rw [← χ.map_add_eq_mul]
  congr 1
  have hne : v j-v s ≠ 0 := sub_ne_zero.mpr hjs
  field_simp
  ring

lemma weighted_character_identity {k : ℕ} (v : Fin k → F) (f : Fin k → F → ℂ)
    {j s : Fin k} (hjs : v j ≠ v s) (χ : AddChar F ℂ) :
    weightedLinearAverage v f χ =
      linearAverage v (fun i y ↦ f i y*twoSlopePhase v j s χ i y) := by
  unfold weightedLinearAverage linearAverage
  rw [expect_comm]
  apply expect_congr rfl
  intro d _
  rw [mul_expect]
  apply expect_congr rfl
  intro x _
  rw [prod_mul_distrib,twoSlopePhase_product v hjs]
  exact mul_comm _ _

/-- Two nondistinguished slopes absorb the character of the common difference,
so weighting does not increase the required uniformity order. -/
theorem weighted_distinct_slopes_bound (n : ℕ) (v : Fin (n+3) → F)
    (hv : Function.Injective v) (f : Fin (n+3) → F → ℂ)
    (hf : ∀ i x, ‖f i x‖ ≤ 1) (w : F → ℂ) (i : Fin (n+3))
    {η : ℝ} (hη : 0 ≤ η)
    (hU : uniformityPower (n+1) (f i) ≤ η^(2^(n+2))) :
    ‖weightedLinearAverage v f w‖ ≤ fourierMass w*η := by
  apply weighted_expect_fourier_bound
  intro χ
  let j : Fin (n+3) := i.succAbove 0
  let s : Fin (n+3) := i.succAbove 1
  have hij : i ≠ j := (Fin.succAbove_ne i 0).symm
  have his : i ≠ s := (Fin.succAbove_ne i 1).symm
  have hjs : j ≠ s := by
    intro h
    have hh := Fin.succAbove_right_injective h
    exact (by intro h01; have ht := congrArg Fin.val h01; simp at ht : (0 : Fin (n+2)) ≠ 1) hh
  let g : Fin (n+3) → F → ℂ := fun t y ↦ f t y*twoSlopePhase v j s χ t y
  have hg (t : Fin (n+3)) (y : F) : ‖g t y‖ ≤ 1 := by
    simpa only [g,norm_mul,twoSlopePhase_norm,mul_one] using hf t y
  have hi : g i = f i := by
    funext y
    simp only [g,twoSlopePhase_off v j s χ hij his,mul_one]
  have h := distinct_slopes_bound (n+1) v hv g hg i
  rw [hi] at h
  have hbound := le_of_pow_le_pow_left₀ (by positivity : 2^(n+2) ≠ 0) hη (h.trans hU)
  change ‖weightedLinearAverage v f χ‖ ≤ η
  rw [weighted_character_identity v f (fun h ↦ hjs (hv h)) χ]
  exact hbound


lemma weighted_replace_sub {k : ℕ} (v : Fin (k+1) → F) (f g : Fin (k+1) → F → ℂ)
    (w : F → ℂ) (i : Fin (k+1)) (hoff : ∀ j, j ≠ i → f j = g j) :
    weightedLinearAverage v f w-weightedLinearAverage v g w =
      weightedLinearAverage v (replace g i (fun x ↦ f i x-g i x)) w := by
  unfold weightedLinearAverage
  rw [← expect_sub_distrib]
  apply expect_congr rfl
  intro d _
  rw [← mul_sub,← expect_sub_distrib]
  congr 1
  apply expect_congr rfl
  intro x _
  rw [Fin.prod_univ_succAbove (fun j ↦ f j (x+v j*d)) i,
    Fin.prod_univ_succAbove (fun j ↦ g j (x+v j*d)) i,
    Fin.prod_univ_succAbove (fun j ↦ replace g i (fun x ↦ f i x-g i x) j (x+v j*d)) i]
  have he (j : Fin k) : f (i.succAbove j) = g (i.succAbove j) := hoff _ (Fin.succAbove_ne i j)
  simp only [replace,if_true,if_neg (Fin.succAbove_ne i _),he]
  ring

lemma weighted_blend_step {k : ℕ} (v : Fin (k+1) → F) (f g w : F → ℂ)
    {j : ℕ} (hj : j < k+1) :
    weightedLinearAverage v (blend f g (j+1)) w-weightedLinearAverage v (blend f g j) w =
      weightedLinearAverage v (replace (blend f g j) ⟨j,hj⟩ (fun x ↦ f x-g x)) w := by
  have he := weighted_replace_sub v (blend f g (j+1)) (blend f g j) w ⟨j,hj⟩ (by
    intro i hi
    have hne : (i : ℕ) ≠ j := by intro hh; apply hi; exact Fin.ext hh
    have hh : (i : ℕ) < j+1 ↔ (i : ℕ) < j := by omega
    simp only [blend,hh])
  simpa only [blend,show j < j+1 by omega,if_true,lt_self_iff_false,if_false] using he

/-- Quantitative counting comparison for at least three distinct slopes with
an arbitrary step weight. -/
theorem weighted_counting_difference (n : ℕ) (v : Fin (n+3) → F)
    (hv : Function.Injective v) (f g w : F → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1)
    (hfg : ∀ x, ‖f x-g x‖ ≤ 1) {η : ℝ} (hη : 0 ≤ η)
    (hU : uniformityPower (n+1) (fun x ↦ f x-g x) ≤ η^(2^(n+2))) :
    ‖weightedLinearAverage v (fun _ ↦ f) w-weightedLinearAverage v (fun _ ↦ g) w‖ ≤
      (n+3 : ℕ)*fourierMass w*η := by
  let H : ℕ → ℂ := fun j ↦ weightedLinearAverage v (blend f g j) w
  have hstep (j : ℕ) (hj : j < n+3) : ‖H (j+1)-H j‖ ≤ fourierMass w*η := by
    let i : Fin (n+3) := ⟨j,hj⟩
    let f' := replace (blend f g j) i (fun x ↦ f x-g x)
    have hf' (s : Fin (n+3)) (x : F) : ‖f' s x‖ ≤ 1 := by
      dsimp [f',replace,blend]
      split_ifs <;> first | exact hfg x | exact hf x | exact hg x
    have he : f' i = fun x ↦ f x-g x := by funext x; simp only [f',replace,if_true]
    have hh := weighted_distinct_slopes_bound n v hv f' hf' w i hη
      (by rw [he]; exact hU)
    simpa only [H,weighted_blend_step v f g w hj,f',i] using hh
  have hzero : H 0 = weightedLinearAverage v (fun _ ↦ g) w := by dsimp [H]; rw [blend_zero]
  have hfull : H (n+3) = weightedLinearAverage v (fun _ ↦ f) w := by dsimp [H]; rw [blend_full]
  rw [← hfull,← hzero,← sum_range_sub H (n+3)]
  calc
    _ ≤ ∑ j ∈ range (n+3), ‖H (j+1)-H j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range (n+3), fourierMass w*η := sum_le_sum (fun j hj ↦ hstep j (mem_range.mp hj))
    _ = _ := by simp [mul_assoc]

#print axioms weighted_counting_difference

#print axioms weighted_distinct_slopes_bound
end Erdos3StepWeightedCounting
