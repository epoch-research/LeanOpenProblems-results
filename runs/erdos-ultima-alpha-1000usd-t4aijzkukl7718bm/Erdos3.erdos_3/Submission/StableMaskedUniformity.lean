import Submission.BohrPatternGeometry

/-! Local character tests can be bounded by the ambient uniformity of their
zero extensions. The two density costs and the stable-window boundary error
are retained explicitly; a Bohr window is never treated as a group. -/
namespace Erdos3StableMaskedUniformity
open Finset Erdos3BohrPatternGeometry Erdos3DifferenceStepCounting
  Erdos3StepWeightedCounting Erdos3FiniteUniformity Erdos3CorrelationSifting
  Erdos3RelativeSpectrumPhase Erdos3RelativeStableBohr Erdos3FiniteBohr
  Erdos3StableWindowCounting
open scoped BigOperators Classical
set_option maxHeartbeats 5000000

variable {G I : Type*} [AddCommGroup G] [Fintype G] [Fintype I]

noncomputable def mask (W : Finset G) (f : G → ℂ) (x : G) : ℂ :=
  if x ∈ W then f x else 0

lemma mask_norm_le (W : Finset G) (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (x : G) :
    ‖mask W f x‖ ≤ 1 := by
  unfold mask
  split_ifs <;> simp_all

lemma product_mask (W : Finset G) (s : I → G) (f : I → G → ℂ) (t : G) :
    (∏ i : I, mask W (f i) (t+s i)) =
      (interiorMask W s t : ℂ)*(∏ i : I, f i (t+s i)) := by
  have he (i : I) : mask W (f i) (t+s i) =
      (indicator W (t+s i) : ℂ)*f i (t+s i) := by
    by_cases h : t+s i ∈ W <;> simp [mask,indicator,h]
  simp only [he,prod_mul_distrib,interiorMask,Complex.ofReal_prod]

lemma mask_boundary_error_complex (C : Finset (AddChar G ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (s : I → G) (hs : ∀ i, s i ∈ bohr C (relativeWidth C z r))
    (H : G → ℂ) (hH : ∀ t, ‖H t‖ ≤ 1) :
    ‖(𝔼 t : bohr C r, H t)-
      (𝔼 t : bohr C r, (interiorMask (bohr C r) s t : ℂ)*H t)‖ ≤
      (Fintype.card I : ℝ)/(z : ℝ) := by
  rw [← expect_sub_distrib]
  have he (t : G) : H t-(interiorMask (bohr C r) s t : ℂ)*H t =
      ((1-interiorMask (bohr C r) s t : ℝ) : ℂ)*H t := by push_cast; ring
  simp only [he]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply le_trans _ (boundary_mass_le C hr hz hstable s hs)
  apply expect_le_expect
  intro t _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (interiorMask_bounds _ _ _).2)]
  exact (mul_le_mul_of_nonneg_left (hH t)
    (sub_nonneg.mpr (interiorMask_bounds _ _ _).2)).trans_eq (mul_one _)

lemma supported_expect (W : Finset G) (hW : W.Nonempty) (H : G → ℂ)
    (hsupp : ∀ x, x ∉ W → H x = 0) :
    (𝔼 x : G, H x) = (density W : ℂ)*(𝔼 x : W, H x) := by
  rw [← expect_normalized_mul_complex W hW H,mul_expect]
  apply expect_congr rfl
  intro x _
  have hpos := density_pos W hW
  have hc : (density W : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  by_cases hx : x ∈ W
  · simp only [normalized,indicator,if_pos hx,
      Complex.ofReal_div,Complex.ofReal_one]
    field_simp [hc]
  · simp [normalized,indicator,hx,hsupp x hx]

variable {F : Type*} [Field F] [Fintype F]

noncomputable def localDifferenceAverage {k : ℕ} (W B : Finset F) (v : Fin k → F)
    (f : Fin k → F → ℂ) : ℂ :=
  𝔼 b : B, 𝔼 c : B, 𝔼 t : W, ∏ i : Fin k, f i (t+v i*((c : F)-b))

lemma difference_masked_supported {k : ℕ} (W B : Finset F) (hW : W.Nonempty)
    (v : Fin k → F) (i₀ : Fin k) (hv₀ : v i₀ = 0) (f : Fin k → F → ℂ) :
    differenceAverage B v (fun i ↦ mask W (f i)) =
      (density W : ℂ)*localDifferenceAverage W B v (fun i ↦ mask W (f i)) := by
  unfold differenceAverage localDifferenceAverage
  rw [mul_expect]
  apply expect_congr rfl
  intro b _
  rw [mul_expect]
  apply expect_congr rfl
  intro c _
  apply supported_expect W hW
  intro x hx
  apply prod_eq_zero (mem_univ i₀)
  simp [hv₀,mask,hx]

lemma local_masking_error (n : ℕ) (B : Finset F) (hB : B.Nonempty)
    (v : Fin (n+3) → F) (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (hs : ∀ b c : B, ∀ i, v i*((c : F)-b) ∈ bohr C (relativeWidth C z r))
    (f : Fin (n+3) → F → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1) :
    ‖localDifferenceAverage (bohr C r) B v f-
      localDifferenceAverage (bohr C r) B v (fun i ↦ mask (bohr C r) (f i))‖ ≤
      (n+3 : ℕ)/(z : ℝ) := by
  letI : Nonempty B := hB.to_subtype
  unfold localDifferenceAverage
  rw [← expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply expect_le univ_nonempty
  intro b _
  rw [← expect_sub_distrib]
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  apply expect_le univ_nonempty
  intro c _
  simp only [product_mask]
  simpa only [Fintype.card_fin] using mask_boundary_error_complex C hr hz hstable
    (fun i ↦ v i*((c : F)-b)) (hs b c)
    (fun t ↦ ∏ i : Fin (n+3), f i (t+v i*((c : F)-b)))
    (fun t ↦ by rw [norm_prod]; exact prod_le_one (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hf i _))

/-- Ambient uniformity of one masked function controls the normalized local
configuration average. The bound includes both density losses and boundary. -/
theorem stable_window_uniformity_bound (n : ℕ) (B : Finset F) (hB : B.Nonempty)
    (v : Fin (n+3) → F) (hv : Function.Injective v) (i₀ : Fin (n+3)) (hv₀ : v i₀ = 0)
    (C : Finset (AddChar F ℂ)) {r : ℝ} (hr : 0 < r)
    {z : ℕ} (hz : 0 < z) (hstable : RelativeStable C z r)
    (hs : ∀ b c : B, ∀ i, v i*((c : F)-b) ∈ bohr C (relativeWidth C z r))
    (f : Fin (n+3) → F → ℂ) (hf : ∀ i x, ‖f i x‖ ≤ 1) (i : Fin (n+3))
    {η : ℝ} (hη : 0 ≤ η)
    (hU : uniformityPower (n+1) (mask (bohr C r) (f i)) ≤ η^(2^(n+2))) :
    ‖localDifferenceAverage (bohr C r) B v f‖ ≤
      η/(density (bohr C r)*density B)+(n+3 : ℕ)/(z : ℝ) := by
  have hW : (bohr C r).Nonempty := ⟨0,bohr_zero C hr.le⟩
  have hWp := density_pos (bohr C r) hW
  have hBp := density_pos B hB
  have hglobal := weighted_distinct_slopes_bound n v hv
    (fun i ↦ mask (bohr C r) (f i))
    (fun i x ↦ mask_norm_le _ _ (hf i) x) (diffWeight B) i hη hU
  rw [diffWeight_fourierMass B hB,← differenceAverage_eq_weighted B hB,
    difference_masked_supported (bohr C r) B hW v i₀ hv₀ f,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hWp] at hglobal
  have hm : ‖localDifferenceAverage (bohr C r) B v (fun i ↦ mask (bohr C r) (f i))‖ ≤
      η/(density (bohr C r)*density B) := by
    apply (le_div_iff₀ (mul_pos hWp hBp)).mpr
    have h := mul_le_mul_of_nonneg_right hglobal hBp.le
    have he : (1/density B*η)*density B = η := by field_simp
    rw [he] at h
    nlinarith only [h]
  calc
    _ ≤ ‖localDifferenceAverage (bohr C r) B v f-
        localDifferenceAverage (bohr C r) B v (fun i ↦ mask (bohr C r) (f i))‖+
        ‖localDifferenceAverage (bohr C r) B v (fun i ↦ mask (bohr C r) (f i))‖ :=
      by simpa only [norm_sub_rev,add_comm] using
        norm_le_insert (localDifferenceAverage (bohr C r) B v (fun i ↦ mask (bohr C r) (f i)))
          (localDifferenceAverage (bohr C r) B v f)
    _ ≤ (n+3 : ℕ)/(z : ℝ)+η/(density (bohr C r)*density B) :=
      add_le_add (local_masking_error n B hB v C hr hz hstable hs f hf) hm
    _ = _ := add_comm _ _

#print axioms stable_window_uniformity_bound
end Erdos3StableMaskedUniformity
