import Submission.FeatureLipschitzEnvelope
import Submission.LocalizedPatternCriterion

/-! The small L2 error in a coarse/fine decomposition has no localization loss:
all base-point marginals are uniform, even when differences are restricted.
Only the arbitrarily small fine uniformity residual pays inverse step density. -/
namespace Erdos3StrongLocalizedCounting
open Finset Erdos3ClippedWeakRegularity Erdos3ConvexLeastSquares
  Erdos3StableWindowCounting Erdos3RobustTopDegreeCounting
  Erdos3LocalizedPatternCriterion Erdos3CorrelationSifting
  Erdos3FiniteUniformity Erdos3RelativeStableBohr Erdos3FiniteBohr
open scoped BigOperators Classical
set_option maxHeartbeats 5000000

variable {G I D : Type*} [AddCommGroup G] [Fintype G] [Fintype I] [Fintype D] [Nonempty D]

/-- Uniform base-point marginals give an L2 counting bound independent of the
step distribution, its support, and its density. -/
theorem translated_count_L2_bound (s : D → I → G) (f g : G → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (herr : squaredError f g ≤ ε^2) :
    |(𝔼 d : D, 𝔼 x : G, ∏ i : I, f (x+s d i))-
      (𝔼 d : D, 𝔼 x : G, ∏ i : I, g (x+s d i))| ≤ (Fintype.card I : ℝ)*ε := by
  have he := mean_abs_le_of_mean_square (fun x : G ↦ f x-g x) hε herr
  have hm (d : D) (i : I) : (𝔼 x : G, |f (x+s d i)-g (x+s d i)|) ≤ ε := by
    have hshift := Fintype.expect_equiv (Equiv.addRight (s d i))
      (fun x : G ↦ |f (x+s d i)-g (x+s d i)|) (fun x : G ↦ |f x-g x|) (fun _ ↦ rfl)
    exact hshift.trans_le he
  rw [← expect_sub_distrib]
  apply (Finset.abs_expect_le _ _).trans
  apply expect_le univ_nonempty
  intro d _
  rw [← expect_sub_distrib]
  calc
    _ ≤ 𝔼 x : G, |(∏ i : I, f (x+s d i))-(∏ i : I, g (x+s d i))| := Finset.abs_expect_le _ _
    _ ≤ 𝔼 x : G, ∑ i : I, |f (x+s d i)-g (x+s d i)| := by
      apply expect_le_expect
      intro x _
      apply abs_prod_sub_prod_le
      · intro i _; rw [abs_of_nonneg (hf _).1]; exact (hf _).2
      · intro i _; rw [abs_of_nonneg (hg _).1]; exact (hg _).2
    _ = ∑ i : I, 𝔼 x : G, |f (x+s d i)-g (x+s d i)| := expect_sum_comm _ _ _
    _ ≤ ∑ _i : I, ε := sum_le_sum (fun i _ ↦ hm d i)
    _ = _ := by simp

variable {F : Type*} [Field F] [Fintype F]

lemma difference_L2_bound {k : ℕ} (B : Finset F) (hB : B.Nonempty)
    (v : Fin k → F) (f g : F → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (herr : squaredError f g ≤ ε^2) :
    |differenceRealAverage B v f-differenceRealAverage B v g| ≤ (k : ℝ)*ε := by
  letI : Nonempty B := hB.to_subtype
  rw [differenceRealAverage_product,differenceRealAverage_product]
  simpa only [Fintype.card_fin] using translated_count_L2_bound
    (fun (p : B × B) i ↦ v i*((p.2 : F)-p.1)) f g hf hg hε herr

/-- Coarse/fine counting: epsilon is independent of the inverse step density,
while eta can be prescribed after the coarse complexity has been bounded. -/
theorem strong_difference_counting (n : ℕ) (B : Finset F) (hB : B.Nonempty)
    (v : Fin (n+3) → F) (hv : Function.Injective v) (f g g' : F → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hg' : ∀ x, 0 ≤ g' x ∧ g' x ≤ 1) {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hU : uniformityPower (n+1) (fun x ↦ ((f x-g' x : ℝ) : ℂ)) ≤ η^(2^(n+2)))
    (hclose : squaredError g g' ≤ ε^2) :
    |differenceRealAverage B v f-differenceRealAverage B v g| ≤
      (n+3 : ℕ)*(η/density B+ε) := by
  have h₁ := real_difference_counting_bound n B hB v hv f g' hf hg' hη hU
  have h₂ := difference_L2_bound B hB v g' g hg' hg hε
    (by rw [squaredError_symm g' g]; exact hclose)
  calc
    _ ≤ |differenceRealAverage B v f-differenceRealAverage B v g'|+
        |differenceRealAverage B v g'-differenceRealAverage B v g| := abs_sub_le _ _ _
    _ ≤ ((n+3 : ℕ)*η)/density B+(n+3 : ℕ)*ε := add_le_add h₁ h₂
    _ = _ := by ring

/-- Adding the local sampled-factor approximation gives three separate error
terms: fine uniformity, coarse/fine L2 error, and local factor L2 error. -/
theorem strong_localized_counting_bridge (n : ℕ) (B : Finset F) (hB : B.Nonempty)
    (v : Fin (n+3) → F) (hv : Function.Injective v)
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r) {z : ℕ} (hz : 0 < z)
    (hstable : RelativeStable C z r)
    (hs : ∀ b c : B, ∀ i, v i*((c : F)-b) ∈ bohr C (relativeWidth C z r))
    (f g g' : F → ℝ) (h : F → F → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hg' : ∀ x, 0 ≤ g' x ∧ g' x ≤ 1) (hh : ∀ a x, 0 ≤ h a x ∧ h a x ≤ 1)
    {η ε τ κ : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε) (hκ : 0 ≤ κ)
    (hU : uniformityPower (n+1) (fun x ↦ ((f x-g' x : ℝ) : ℂ)) ≤ η^(2^(n+2)))
    (hclose : squaredError g g' ≤ ε^2)
    (herr : ∀ a, (𝔼 t : bohr C r, (g (a+t)-h a t)^2) ≤ τ)
    (hbudget : τ+1/(z : ℝ) ≤ κ^2) :
    |differenceRealAverage B v f-
      (𝔼 a : F, windowPatternAverage (bohr C r)
        (fun (p : B × B) i ↦ v i*((p.2 : F)-p.1)) (h a))| ≤
      (n+3 : ℕ)*(η/density B+ε+κ) := by
  letI : Nonempty B := hB.to_subtype
  have h₁ := strong_difference_counting n B hB v hv f g g' hf hg hg' hη hε hU hclose
  have h₂ := averaged_local_factor_counting_difference C hr hz hstable
    (fun (p : B × B) i ↦ v i*((p.2 : F)-p.1)) (fun p i ↦ hs p.1 p.2 i)
    g h hg hh hκ herr hbudget
  rw [← differenceRealAverage_product] at h₂
  simp only [Fintype.card_fin] at h₂
  calc
    _ ≤ |differenceRealAverage B v f-differenceRealAverage B v g|+
        |differenceRealAverage B v g-(𝔼 a : F, windowPatternAverage (bohr C r)
          (fun (p : B × B) i ↦ v i*((p.2 : F)-p.1)) (h a))| := abs_sub_le _ _ _
    _ ≤ (n+3 : ℕ)*(η/density B+ε)+(n+3 : ℕ)*κ := add_le_add h₁ h₂
    _ = _ := by ring

#print axioms translated_count_L2_bound
#print axioms strong_difference_counting
#print axioms strong_localized_counting_bridge
end Erdos3StrongLocalizedCounting
