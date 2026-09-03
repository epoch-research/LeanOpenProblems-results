import Submission.LocalFreimanExtension

/-! A quantitative finite Bogolyubov lemma: 2H-2H contains a constant-radius
Bohr set with rank at most 8/density(H)^2. -/
namespace Erdos3FiniteBogolyubov
open Finset Erdos3FiniteBohr Erdos3FiniteFourier Erdos3QuadraticFourAPBarrier
  Erdos3LinearFormsUniformity
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 4500000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def cindicator (H : Finset G) (x : G) : ℂ := if x ∈ H then 1 else 0
noncomputable def density (H : Finset G) : ℝ := (H.card : ℝ)/(Fintype.card G : ℝ)
noncomputable def fourCorr (H : Finset G) : G → ℂ := complexCorr (complexCorr (cindicator H))

lemma density_pos (H : Finset G) (hH : H.Nonempty) : 0 < density H := by
  unfold density
  exact div_pos (by exact_mod_cast hH.card_pos) (by exact_mod_cast Fintype.card_pos)

lemma cindicator_mean (H : Finset G) : (𝔼 x : G, cindicator H x) = (density H : ℂ) := by
  simp [cindicator,density,Fintype.expect_eq_sum_div_card]

lemma cindicator_parseval (H : Finset G) :
    (∑ χ : AddChar G ℂ, ‖hat (cindicator H) χ‖^2) = density H := by
  rw [parseval]
  have he (x : G) : ‖cindicator H x‖^2 = if x ∈ H then (1 : ℝ) else 0 := by
    by_cases hx : x ∈ H <;> simp [cindicator,hx]
  simp_rw [he]
  simp [density,Fintype.expect_eq_sum_div_card]

lemma fourCorr_fourier (H : Finset G) (x : G) :
    fourCorr H x = ∑ χ : AddChar G ℂ, ((‖hat (cindicator H) χ‖^4 : ℝ) : ℂ)*χ x := by
  rw [inversion (fourCorr H)]
  apply sum_congr rfl
  intro χ _
  unfold fourCorr
  rw [hat_complexCorr,hat_complexCorr]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖hat (cindicator H) χ‖)]
  congr 2
  ring

lemma cindicator_corr_support (H : Finset G) (x : G) (hx : complexCorr (cindicator H) x ≠ 0) : x ∈ H-H := by
  by_contra hn
  apply hx
  apply expect_eq_zero
  intro y _
  by_cases hy : y ∈ H
  · have hyx : y+x ∉ H := by
      intro hh
      apply hn
      exact mem_sub.mpr ⟨y+x,hh,y,hy,by abel⟩
    simp [cindicator,hyx]
  · simp [cindicator,hy]

lemma fourCorr_support (H : Finset G) (x : G) (hx : fourCorr H x ≠ 0) : x ∈ (2 : ℕ) • H-(2 : ℕ) • H := by
  by_contra hn
  apply hx
  apply expect_eq_zero
  intro y _
  by_cases hy : complexCorr (cindicator H) y = 0
  · simp [hy]
  · have hyx : complexCorr (cindicator H) (y+x) = 0 := by
      by_contra hne
      obtain ⟨a,ha,b,hb,hab⟩ := mem_sub.mp (cindicator_corr_support H (y+x) hne)
      obtain ⟨c,hc,d,hd,hcd⟩ := mem_sub.mp (cindicator_corr_support H y hy)
      apply hn
      rw [two_nsmul]
      apply mem_sub.mpr
      refine ⟨a+d,add_mem_add ha hd,c+b,add_mem_add hc hb,?_⟩
      have he : (a+d)-(c+b) = (a-b)-(c-d) := by abel
      rw [he,hab,hcd]
      abel
    simp [hyx]

/-- An explicit spectrum gives a positive fourfold convolution on its radius-1/2
Bohr set, and therefore puts that Bohr set inside 2H-2H. -/
theorem bogolyubov (H : Finset G) (hH : H.Nonempty) :
    ∃ D : Finset (AddChar G ℂ),
      (D.card : ℝ) ≤ 8/(density H)^2 ∧
      (∀ x ∈ bohr D (1/2), (density H)^4/4 ≤ (fourCorr H x).re) ∧
      bohr D (1/2) ⊆ (2 : ℕ) • H-(2 : ℕ) • H := by
  let α := density H
  have hα : 0 < α := density_pos H hH
  let a : AddChar G ℂ → ℝ := fun χ ↦ ‖hat (cindicator H) χ‖^2
  let w : AddChar G ℂ → ℝ := fun χ ↦ ‖hat (cindicator H) χ‖^4
  let θ : ℝ := α^3/8
  let D := univ.filter (fun χ ↦ θ ≤ a χ)
  have ha (χ : AddChar G ℂ) : 0 ≤ a χ := sq_nonneg _
  have hw (χ : AddChar G ℂ) : 0 ≤ w χ := pow_nonneg (norm_nonneg _) _
  have hwa (χ : AddChar G ℂ) : w χ = (a χ)^2 := by dsimp [w,a]; ring
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hsum : (∑ χ : AddChar G ℂ, a χ) = α := cindicator_parseval H
  have hcard : (D.card : ℝ) ≤ 8/α^2 := by
    have hh : θ*(D.card : ℝ) ≤ α := by
      calc
        _ = ∑ _χ ∈ D, θ := by simp [mul_comm]
        _ ≤ ∑ χ ∈ D, a χ := sum_le_sum (fun χ hχ ↦ (mem_filter.mp hχ).2)
        _ ≤ ∑ χ : AddChar G ℂ, a χ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun χ _ _ ↦ ha χ)
        _ = α := hsum
    apply (le_div_iff₀ (sq_pos_of_pos hα)).mpr
    dsimp [θ] at hh
    nlinarith only [hh,hα]
  have htail : (∑ χ : AddChar G ℂ, if χ ∈ D then 0 else w χ) ≤ α^4/8 := by
    calc
      _ ≤ ∑ χ : AddChar G ℂ, θ*a χ := by
        apply sum_le_sum
        intro χ _
        by_cases hχ : χ ∈ D
        · rw [if_pos hχ]
          exact mul_nonneg hθ.le (ha χ)
        · have hh : a χ < θ := by simpa only [D,mem_filter,mem_univ,true_and,not_le] using hχ
          rw [if_neg hχ,hwa]
          nlinarith [mul_le_mul_of_nonneg_right hh.le (ha χ)]
      _ = α^4/8 := by rw [← mul_sum,hsum]; dsimp [θ]; ring
  have hmass : α^4 ≤ ∑ χ : AddChar G ℂ, w χ := by
    have htriv : w 1 = α^4 := by
      dsimp [w]
      have hh : hat (cindicator H) 1 = (α : ℂ) := by
        simpa only [hat,AddChar.one_apply,map_one,mul_one] using cindicator_mean H
      rw [hh,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hα]
    rw [← htriv]
    exact single_le_sum (fun χ _ ↦ hw χ) (mem_univ 1)
  have hpositive (x : G) (hx : x ∈ bohr D (1/2)) : α^4/4 ≤ (fourCorr H x).re := by
    have hre : (fourCorr H x).re = ∑ χ : AddChar G ℂ, w χ*(χ x).re := by
      rw [fourCorr_fourier,Complex.re_sum]
      apply sum_congr rfl
      intro χ _
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,w]
    have hpt (χ : AddChar G ℂ) :
        (1/2)*w χ-2*(if χ ∈ D then 0 else w χ) ≤ w χ*(χ x).re := by
      have hre0 : -1 ≤ (χ x).re := by
        have hh := (abs_le.mp ((Complex.abs_re_le_norm _).trans_eq (χ.norm_apply x))).1
        exact hh
      by_cases hχ : χ ∈ D
      · have hn := mem_bohr.mp hx χ hχ
        have hh := (abs_le.mp (Complex.abs_re_le_norm (χ x-1))).1
        simp only [Complex.sub_re,Complex.one_re] at hh
        have hre1 : (1/2 : ℝ) ≤ (χ x).re := by linarith
        rw [if_pos hχ,mul_zero,sub_zero]
        nlinarith [mul_le_mul_of_nonneg_left hre1 (hw χ)]
      · rw [if_neg hχ]
        nlinarith [hw χ,mul_le_mul_of_nonneg_left hre0 (hw χ)]
    have hh := sum_le_sum (fun χ (_ : χ ∈ univ) ↦ hpt χ)
    rw [sum_sub_distrib,← mul_sum,← mul_sum,← hre] at hh
    linarith
  refine ⟨D,hcard,hpositive,?_⟩
  intro x hx
  apply fourCorr_support H x
  intro hz
  have hh := hpositive x hx
  rw [hz,Complex.zero_re] at hh
  have hp : 0 < α^4 := pow_pos hα 4
  linarith

#print axioms bogolyubov
end Erdos3FiniteBogolyubov
