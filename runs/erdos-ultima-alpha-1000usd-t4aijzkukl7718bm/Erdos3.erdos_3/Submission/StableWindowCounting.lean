import Submission.DifferenceStepCounting
import Submission.RobustTopDegreeCounting
import Submission.RelativeStableBohr

/-! Local mean-square approximations transfer to configuration counts on a
stable Bohr window without an inverse-window-density loss. The stability
error is retained explicitly. -/
namespace Erdos3StableWindowCounting
open Finset Erdos3FiniteBohr Erdos3BohrTranslation Erdos3RelativeStableBohr
  Erdos3CrootSisaskL2 Erdos3RobustTopDegreeCounting Erdos3FiniteSampling
open scoped BigOperators Classical
set_option maxHeartbeats 4000000

variable {G : Type*} [AddCommGroup G] [Fintype G]

lemma bounded_sub_square (f g : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (x : G) : |(f x-g x)^2| ≤ 1 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  have hh : |f x-g x| ≤ 1 := abs_le.mpr
    ⟨by linarith [(hf x).1,(hg x).2],by linarith [(hf x).2,(hg x).1]⟩
  simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg _) hh 2

/-- Translation of the local mean-square error costs at most the stability
tolerance, because both functions are [0,1]-valued. -/
lemma shifted_mean_square_le (C : Finset (AddChar G ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (f g : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) {ε : ℝ}
    (herr : (𝔼 t : bohr C r, (f t-g t)^2) ≤ ε)
    {s : G} (hs : s ∈ bohr C (relativeWidth C z r)) :
    (𝔼 t : bohr C r, (f (t+s)-g (t+s))^2) ≤ ε+1/(z : ℝ) := by
  have h := smooth_bohr_translation_le C hr.le (relativeWidth_pos C hz hr).le
    (by positivity : (0 : ℝ) ≤ 1/z) (by norm_num : (0 : ℝ) ≤ 1) hstable
    (fun x ↦ (f x-g x)^2) (bounded_sub_square f g hf hg) hs 0
  simp only [smooth,zero_add,mul_one] at h
  have he : (𝔼 t : bohr C r, (f (s+t)-g (s+t))^2) =
      𝔼 t : bohr C r, (f (t+s)-g (t+s))^2 := by simp only [add_comm s]
  rw [he] at h
  linarith [(abs_le.mp h).2]

lemma mean_abs_le_of_mean_square {X : Type*} [Fintype X] [Nonempty X]
    (e : X → ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (he : (𝔼 x : X, (e x)^2) ≤ κ^2) :
    (𝔼 x : X, |e x|) ≤ κ := by
  have h := expect_mul_sq_le_sq_mul_sq univ (fun x : X ↦ |e x|) (fun _ ↦ (1 : ℝ))
  simp only [mul_one,sq_abs,one_pow,Fintype.expect_const] at h
  exact le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0) hκ (h.trans he)

variable {I D : Type*} [Fintype I] [Fintype D]

noncomputable def windowPatternAverage (W : Finset G) (s : D → I → G) (f : G → ℝ) : ℝ :=
  𝔼 d : D, 𝔼 t : W, ∏ i : I, f (t+s d i)

/-- Each shifted marginal is close to uniform on the stable window. This
converts a single normalized L2 approximation into an entire counting bound. -/
theorem stable_window_counting_difference [Nonempty D]
    (C : Finset (AddChar G ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (s : D → I → G) (hs : ∀ d i, s d i ∈ bohr C (relativeWidth C z r))
    (f g : G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) {ε κ : ℝ} (hκ : 0 ≤ κ)
    (herr : (𝔼 t : bohr C r, (f t-g t)^2) ≤ ε)
    (hbudget : ε+1/(z : ℝ) ≤ κ^2) :
    |windowPatternAverage (bohr C r) s f-windowPatternAverage (bohr C r) s g| ≤
      (Fintype.card I : ℝ)*κ := by
  letI : Nonempty (bohr C r) := ⟨⟨0,bohr_zero C hr.le⟩⟩
  have he (d : D) (i : I) : (𝔼 t : bohr C r, |f (t+s d i)-g (t+s d i)|) ≤ κ :=
    mean_abs_le_of_mean_square _ hκ
      ((shifted_mean_square_le C hr hz hstable f g hf hg herr (hs d i)).trans hbudget)
  unfold windowPatternAverage
  rw [← expect_sub_distrib]
  apply (Finset.abs_expect_le _ _).trans
  apply expect_le univ_nonempty
  intro d _
  rw [← expect_sub_distrib]
  calc
    _ ≤ 𝔼 t : bohr C r, |(∏ i : I, f (t+s d i))-(∏ i : I, g (t+s d i))| :=
      Finset.abs_expect_le _ _
    _ ≤ 𝔼 t : bohr C r, ∑ i : I, |f (t+s d i)-g (t+s d i)| := by
      apply expect_le_expect
      intro t _
      apply abs_prod_sub_prod_le
      · intro i _; rw [abs_of_nonneg (hf _).1]; exact (hf _).2
      · intro i _; rw [abs_of_nonneg (hg _).1]; exact (hg _).2
    _ = ∑ i : I, 𝔼 t : bohr C r, |f (t+s d i)-g (t+s d i)| := expect_sum_comm _ _ _
    _ ≤ ∑ _i : I, κ := sum_le_sum (fun i _ ↦ he d i)
    _ = _ := by simp

/-- Averaging the base point of a translated window restores a uniform global
base point, exactly and without a density cost. -/
lemma averaged_window_count (W : Finset G) (hW : W.Nonempty)
    (s : D → I → G) (f : G → ℝ) :
    (𝔼 a : G, windowPatternAverage W s (fun t ↦ f (a+t))) =
      𝔼 d : D, 𝔼 x : G, ∏ i : I, f (x+s d i) := by
  letI : Nonempty W := hW.to_subtype
  unfold windowPatternAverage
  rw [expect_comm]
  apply expect_congr rfl
  intro d _
  rw [expect_comm]
  have he (t : W) : (𝔼 a : G, ∏ i : I, f (a+(t+s d i))) =
      𝔼 x : G, ∏ i : I, f (x+s d i) := by
    apply Fintype.expect_equiv (Equiv.addRight (t : G))
    intro a
    change (∏ i : I, f (a+((t : G)+s d i))) = ∏ i : I, f ((a+t)+s d i)
    simp only [add_assoc]
  simp only [he,Fintype.expect_const]

/-- The exact global count can therefore be compared with a different local
factor at every base point, still without an inverse-window-density loss. -/
theorem averaged_local_factor_counting_difference [Nonempty D]
    (C : Finset (AddChar G ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (s : D → I → G) (hs : ∀ d i, s d i ∈ bohr C (relativeWidth C z r))
    (f : G → ℝ) (g : G → G → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ a x, 0 ≤ g a x ∧ g a x ≤ 1) {ε κ : ℝ} (hκ : 0 ≤ κ)
    (herr : ∀ a, (𝔼 t : bohr C r, (f (a+t)-g a t)^2) ≤ ε)
    (hbudget : ε+1/(z : ℝ) ≤ κ^2) :
    |(𝔼 d : D, 𝔼 x : G, ∏ i : I, f (x+s d i))-
      (𝔼 a : G, windowPatternAverage (bohr C r) s (g a))| ≤
      (Fintype.card I : ℝ)*κ := by
  rw [← averaged_window_count (bohr C r) ⟨0,bohr_zero C hr.le⟩,← expect_sub_distrib]
  apply (Finset.abs_expect_le _ _).trans
  exact expect_le univ_nonempty (fun a _ ↦ stable_window_counting_difference C hr hz hstable
    s hs (fun t ↦ f (a+t)) (g a) (fun t ↦ hf _) (hg a) hκ (herr a) hbudget)

#print axioms stable_window_counting_difference
#print axioms averaged_local_factor_counting_difference
end Erdos3StableWindowCounting
