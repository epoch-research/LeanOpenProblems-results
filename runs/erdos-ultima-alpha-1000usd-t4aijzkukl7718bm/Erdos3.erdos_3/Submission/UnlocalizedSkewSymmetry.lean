import Submission.UnlocalizedBilinearExtraction

/-! Symmetry extraction on the full difference domain. This avoids the
exponential support-density loss from early Bohr localization. -/
namespace Erdos3UnlocalizedSkewSymmetry
open Finset Erdos3UnlocalizedBilinearExtraction Erdos3LocalSkewSymmetry
  Erdos3LocalQuadraticIntegration Erdos3QuantitativeSkewSymmetry
  Erdos3BiasedSkewDifferences Erdos3FiniteBohr Erdos3CorrelationSifting
  Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3AveragedAntisymmetry
  Erdos3LocalPhaseDuality
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma fourfold_subset_diffBall_two (T X : Finset G) (hX : X ⊆ T) :
    (X+X)-(X+X) ⊆ diffBall T 2 := by
  intro z hz
  obtain ⟨a,ha,b,hb,c,hc,d,hd,rfl⟩ := mem_fourfold_split X hz
  exact diffBall_add (mem_diffBall_one.mpr (sub_mem_sub (hX ha) (hX hc)))
    (mem_diffBall_one.mpr (sub_mem_sub (hX hb) (hX hd)))

lemma fourfold_subset_diffBall (T D : Finset G) {n : ℕ} (hD : D ⊆ diffBall T n) :
    (D+D)-(D+D) ⊆ diffBall T (4*n) := by
  intro z hz
  obtain ⟨a,ha,b,hb,c,hc,d,hd,rfl⟩ := mem_fourfold_split D hz
  have hh := diffBall_add (diffBall_sub (hD ha) (hD hc)) (diffBall_sub (hD hb) (hD hd))
  simpa only [show n+n+(n+n) = 4*n by omega] using hh

/-- The same two Bogolyubov domains suffice without shrinking T beforehand:
all required fourfold sets are already in the twelve-Freiman extension domain. -/
theorem unlocalized_cross_bohr_symmetry (T X D : Finset G) (hT : T.Nonempty)
    (F : G → AddChar G ℂ) (hF : LocallyAdditive (diffBall T 4 : Set G) F)
    (hX : X.Nonempty) (hD : D.Nonempty) (hXT : X ⊆ T) (hDT : D ⊆ T-T)
    {ε : ℝ} (hcross : ∀ s ∈ X, ∀ t ∈ X, ∀ d ∈ D,
      ‖Erdos3AntidiagonalTwistedEnergy.skewPhase F (s-t) d-1‖ ≤ ε) :
    ∃ E : Finset (AddChar G ℂ),
      (E.card : ℝ) ≤ 8/(density X)^2+8/(density D)^2 ∧
      bohr E (1/2) ⊆ diffBall T 2 ∧
      LocallyAdditive (bohr E (1/2) : Set G) F ∧
      ∀ x ∈ bohr E (1/2), ∀ y ∈ bohr E (1/2), ‖F x y-F y x‖ ≤ 8*ε := by
  have hXdiff : X-X ⊆ diffBall T 1 := fun _ hx ↦ mem_diffBall_one.mpr (sub_subset_sub hXT hXT hx)
  have hXfour := fourfold_subset_diffBall_two T X hXT
  have hDr : D ⊆ diffBall T 1 := fun _ hd ↦ mem_diffBall_one.mpr (hDT hd)
  have hDdiff : D-D ⊆ diffBall T 2 := by
    intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_sub.mp hx
    exact diffBall_sub (hDr ha) (hDr hb)
  have hDfour : (D+D)-(D+D) ⊆ diffBall T 4 := fourfold_subset_diffBall T D hDr
  obtain ⟨E₁,hE₁,_,hsub₁⟩ := Erdos3FiniteBogolyubov.bogolyubov X hX
  obtain ⟨E₂,hE₂,_,hsub₂⟩ := Erdos3FiniteBogolyubov.bogolyubov D hD
  let E := E₁ ∪ E₂
  have hto₁ {x : G} (hx : x ∈ bohr E (1/2)) : x ∈ (X+X)-(X+X) := by
    have hx₁ : x ∈ bohr E₁ (1/2) := mem_bohr.mpr (fun χ hχ ↦ mem_bohr.mp hx χ (mem_union_left _ hχ))
    simpa only [two_nsmul,mem_sub,mem_add] using hsub₁ hx₁
  have hto₂ {x : G} (hx : x ∈ bohr E (1/2)) : x ∈ (D+D)-(D+D) := by
    have hx₂ : x ∈ bohr E₂ (1/2) := mem_bohr.mpr (fun χ hχ ↦ mem_bohr.mp hx χ (mem_union_right _ hχ))
    simpa only [two_nsmul,mem_sub,mem_add] using hsub₂ hx₂
  have hEP : bohr E (1/2) ⊆ diffBall T 4 := fun _ hx ↦ diffBall_mono T hT (by decide) (hXfour (hto₁ hx))
  refine ⟨E,?_,fun _ hx ↦ hXfour (hto₁ hx),?_,?_⟩
  · have hh : (E.card : ℝ) ≤ (E₁.card : ℝ)+(E₂.card : ℝ) := by exact_mod_cast card_union_le E₁ E₂
    exact hh.trans (add_le_add hE₁ hE₂)
  · intro x hx y hy hxy
    exact hF x (hEP hx) y (hEP hy) (hEP hxy)
  · intro x hx y hy
    rw [← norm_skewPhase_error]
    exact cross_control_fourfold hF X D
      (fun _ hh ↦ diffBall_mono T hT (by decide : 1 ≤ 4) (hXdiff hh))
      (fun _ hh ↦ diffBall_mono T hT (by decide : 2 ≤ 4) (hXfour hh))
      (fun _ hh ↦ diffBall_mono T hT (by decide : 1 ≤ 4) (hDr hh))
      (fun _ hh ↦ diffBall_mono T hT (by decide : 2 ≤ 4) (hDdiff hh))
      hDfour hcross (hto₁ hx) (hto₂ hy)

/-- Quantitative symmetry with no initial Bohr-localization cost. -/
theorem exists_unlocalized_bohr_symmetry (T : Finset G) (hT : T.Nonempty)
    (F : G → AddChar G ℂ) (hF : LocallyAdditive (diffBall T 4 : Set G) F)
    (hFdiff : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t)
    {Λ ε : ℝ} (hΛ : 0 < Λ) (hmean : Λ ≤ pairSkewBias T F) (hε : 0 < ε) :
    ∃ E : Finset (AddChar G ℂ),
      (E.card : ℝ) ≤ symmetryRank (density T) Λ ε ∧
      bohr E (1/2) ⊆ diffBall T 2 ∧ LocallyAdditive (bohr E (1/2) : Set G) F ∧
      ∀ x ∈ bohr E (1/2), ∀ y ∈ bohr E (1/2), ‖F x y-F y x‖ ≤ ε := by
  let σ := density T
  let n := symmetrySamples σ Λ ε
  have hσ : 0 < σ := density_pos T hT
  have hn : 0 < n := symmetrySamples_pos σ Λ ε
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hcost : 16*(Fintype.card G : ℝ) ≤ (n : ℝ)*(T.card : ℝ)*(Λ/2)^4*(ε/8)^2 := by
    have hh := symmetrySamples_cost hσ hΛ hε
    change 16 ≤ (n : ℝ)*((T.card : ℝ)/(Fintype.card G : ℝ))*(Λ/2)^4*(ε/8)^2 at hh
    have hh' := mul_le_mul_of_nonneg_right hh hN.le
    convert hh' using 1 <;> field_simp
  obtain ⟨X,D,hX,hD,hXT,hDT,hXsize,hDsize,hcross⟩ := exists_cross_skew_control T hT F hFdiff
    hΛ hmean hn (by positivity : 0 ≤ ε/8) hcost
  obtain ⟨E,hE,hsub,hadd,hsym⟩ := unlocalized_cross_bohr_symmetry T X D hT F hF hX hD hXT hDT hcross
  have hXlow : σ^(n+1)/2 ≤ density X := density_lower_of_sample_card T X n hXsize
  have hDlow : Λ*σ/2 ≤ density D := density_lower_of_difference_card T D Λ hDsize
  have hXpos : 0 < σ^(n+1)/2 := by positivity
  have hDpos : 0 < Λ*σ/2 := by positivity
  have hXrank : 8/(density X)^2 ≤ 32/σ^(2*(n+1)) := by
    calc
      _ ≤ 8/(σ^(n+1)/2)^2 := div_le_div_of_nonneg_left (by norm_num)
        (sq_pos_of_pos hXpos) (pow_le_pow_left₀ hXpos.le hXlow 2)
      _ = _ := by rw [div_pow,← pow_mul,mul_comm (n+1) 2]; ring
  have hDrank : 8/(density D)^2 ≤ 32/(Λ*σ)^2 := by
    calc
      _ ≤ 8/(Λ*σ/2)^2 := div_le_div_of_nonneg_left (by norm_num)
        (sq_pos_of_pos hDpos) (pow_le_pow_left₀ hDpos.le hDlow 2)
      _ = _ := by ring
  refine ⟨E,hE.trans (add_le_add hXrank hDrank),hsub,hadd,?_⟩
  intro x hx y hy
  simpa only [show 8*(ε/8) = ε by ring] using hsym x hx y hy

/-- Large U³ has a polynomial-density correlated direction set and a common
Bohr domain of approximate symmetry, with no early exponential thinning. -/
theorem large_U3_unlocalized_symmetry (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ ε : ℝ} (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) (hε : 0 < ε) :
    ∃ T : Finset G, ∃ F : G → AddChar G ℂ, ∃ a₀ : G, ∃ χ₀ : AddChar G ℂ,
    ∃ E : Finset (AddChar G ℂ),
      0 ∈ T ∧ δ^5/256*(Fintype.card G : ℝ) ≤ unlocalizedLoss δ*(T.card : ℝ) ∧
      F 0 = 0 ∧ (∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t) ∧
      (∀ t ∈ T, δ/2 ≤ ‖hat (derivative f (t+a₀)) (F t+χ₀)‖^2) ∧
      (E.card : ℝ) ≤ symmetryRank (density T) ((δ/2)^8*(density T)^4) ε ∧
      LocallyAdditive (bohr E (1/2) : Set G) F ∧
      ∀ x ∈ bohr E (1/2), ∀ y ∈ bohr E (1/2), ‖F x y-F y x‖ ≤ ε := by
  obtain ⟨T,F,a₀,χ₀,hT0,hsize,hF0,hadd,hdiff,hcoef⟩ := large_U3_unlocalized_bilinear f hf hδ hU
  have hT : T.Nonempty := ⟨0,hT0⟩
  have hσ : 0 < density T := density_pos T hT
  have hmean : (δ/2)^8*(density T)^4 ≤ pairSkewBias T F := by
    have hh := large_coefficients_average_bias_lower T hT
      (fun x ↦ f (x+a₀)) (fun x ↦ f x*χ₀ x) F
      (fun x ↦ hf _) (fun x ↦ by simpa only [norm_mul,AddChar.norm_apply,mul_one] using hf x)
      hdiff (show 0 ≤ δ/2 by positivity)
      (fun t ht ↦ by rw [shifted_mixed_coefficient]; exact hcoef t ht)
    change (δ/2)^8*(density T)^7 ≤ averageSkewBias T F at hh
    rw [averageSkewBias_eq_normalized T hT F] at hh
    apply (mul_le_mul_iff_right₀ (pow_pos hσ 3)).mp
    calc
      _ = (δ/2)^8*(density T)^7 := by ring
      _ ≤ _ := hh
      _ = _ := by ring
  obtain ⟨E,hE,_,hEadd,hsym⟩ := exists_unlocalized_bohr_symmetry T hT F hadd hdiff (by positivity) hmean hε
  exact ⟨T,F,a₀,χ₀,E,hT0,hsize,hF0,hdiff,hcoef,hE,hEadd,hsym⟩

#print axioms large_U3_unlocalized_symmetry
end Erdos3UnlocalizedSkewSymmetry
