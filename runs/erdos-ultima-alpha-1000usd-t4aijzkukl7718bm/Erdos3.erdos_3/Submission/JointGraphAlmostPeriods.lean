import Submission.GraphTripleProjection

/-! One graph sample set supplies both Fourier annihilation and uniform triple
almost-periodicity. Projecting its unique-frequency rows yields simultaneous
almost-periods for every biased skew-phase cubic convolution. -/
namespace Erdos3JointGraphAlmostPeriods
open Finset Erdos3CrootSisaskL2 Erdos3CrootSisaskLp Erdos3CrootSisaskSup
  Erdos3CorrelationSifting Erdos3PopularAlmostPeriods Erdos3SmallDoublingAnnihilation
  Erdos3GraphTripleProjection Erdos3PhaseCubicSmoothing Erdos3FiniteFourier
  Erdos3FrequencyGraph Erdos3GraphSkewAnnihilation Erdos3LocalQuadraticIntegration
  Erdos3LocalSkewSymmetry Erdos3UnlocalizedBilinearExtraction Erdos3BiasedSkewDifferences
  Erdos3AntidiagonalTwistedEnergy
open scoped BigOperators Classical Pointwise ComplexConjugate
set_option maxHeartbeats 6000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma spectrum_bound_from_L2 (A : Finset G) (hA : A.Nonempty) {n : ℕ} (hn : 0 < n)
    (s t : G)
    (hp : sqNorm (fun x ↦ smooth A (indicator A) (x+s)-smooth A (indicator A) (x+t)) ≤
      (8/(n : ℝ))*(A.card : ℝ)) (χ : AddChar G ℂ) :
    (n : ℝ)*(A.card : ℝ)*‖χ (s-t)-1‖^2*‖meanChar A χ‖^4 ≤ 16*((A-A).card : ℝ) := by
  have he := (shifted_smooth_character_bound A s t χ).trans
    (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2*((A-A).card : ℝ)))
  have ha : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have he' := mul_le_mul_of_nonneg_left he hnR.le
  field_simp at he'
  nlinarith only [he']

omit [DecidableEq G] in
lemma triple_bound_from_L2 (A : Finset G) (hA : A.Nonempty) (s t : G) {ε : ℝ} (hε : 0 ≤ ε)
    (hp : sqNorm (fun x ↦ smooth A (indicator A) (x+s)-smooth A (indicator A) (x+t)) ≤
      ε^2*(A.card : ℝ)) (x : G) : |triple A (x+s)-triple A (x+t)| ≤ ε := by
  let g : G → ℝ := fun y ↦ smooth A (indicator A) (y+s)-smooth A (indicator A) (y+t)
  have hg : evenMoment g 1 ≤ ε^(2*1)*((-A).card : ℝ) := by simpa only [evenMoment,sqNorm,card_neg] using hp
  have hh := smooth_abs_le_of_evenMoment_le (-A) hA.neg g (by decide : 0 < 1) hε hg x
  simpa only [g,smooth_sub,smooth_translate,smooth_neg_smooth,triple] using hh

/-- The same sample set has both properties; no intersection of independently
chosen large sets is taken. -/
theorem exists_joint_spectrum_periods (A : Finset G) (hA : A.Nonempty)
    {n : ℕ} (hn : 0 < n) {η ε : ℝ} (hη : 0 < η) (hε : 0 ≤ ε)
    (hL2 : 8 ≤ (n : ℝ)*ε^2)
    (hspec : 16*((A-A).card : ℝ) ≤ (n : ℝ)*(A.card : ℝ)*η^4*ε^2) :
    ∃ X : Finset G, X.Nonempty ∧ X ⊆ A ∧
      A.card^n*A.card ≤ 2*(A+A).card^n*X.card ∧
      (∀ s ∈ X, ∀ t ∈ X, ∀ x, |triple A (x+s)-triple A (x+t)| ≤ ε) ∧
      ∀ s ∈ X, ∀ t ∈ X, ∀ χ : AddChar G ℂ,
        η ≤ ‖meanChar A χ‖ → ‖χ (s-t)-1‖ ≤ ε := by
  obtain ⟨X,hsub,hcard,hper⟩ := exists_many_L2_almost_periods A A hA hA (indicator A) hn
  have hX : X.Nonempty := by
    apply card_pos.mp
    by_contra h
    have hz : X.card = 0 := by omega
    rw [hz,mul_zero] at hcard
    have hp := mul_pos (pow_pos hA.card_pos n) hA.card_pos
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hAr : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hp (s : G) (hs : s ∈ X) (t : G) (ht : t ∈ X) := hper s hs t ht
  simp only [sqNorm_indicator] at hp
  refine ⟨X,hX,hsub,?_,?_,?_⟩
  · convert hcard using 1
    congr 4
    ext x
    simp only [mem_add]
  · intro s hs t ht x
    apply triple_bound_from_L2 A hA s t hε _ x
    exact (hp s hs t ht).trans (mul_le_mul_of_nonneg_right
      ((div_le_iff₀ hnR).mpr (by nlinarith only [hL2])) hAr.le)
  · intro s hs t ht χ hχ
    have hh := spectrum_bound_from_L2 A hA hn s t (hp s hs t ht) χ
    have hl : (n : ℝ)*(A.card : ℝ)*η^4*‖χ (s-t)-1‖^2 ≤
        (n : ℝ)*(A.card : ℝ)*‖χ (s-t)-1‖^2*‖meanChar A χ‖^4 := by
      calc
        _ = (n : ℝ)*(A.card : ℝ)*‖χ (s-t)-1‖^2*η^4 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη.le hχ 4) (by positivity)
    have hpos : 0 < (n : ℝ)*(A.card : ℝ)*η^4 := by positivity
    exact (sq_le_sq₀ (norm_nonneg _) hε).mp
      ((mul_le_mul_iff_right₀ hpos).mp (hl.trans (hh.trans hspec)))

lemma unit_scalar_difference (z a b : ℂ) (hz : ‖z‖ = 1) (ha : ‖a‖ = 1)
    (r s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖z*a*(r : ℂ)-z*b*(s : ℂ)‖ ≤ |r-s|+‖a-b‖ := by
  have he : z*a*(r : ℂ)-z*b*(s : ℂ) = z*(a*((r-s : ℝ) : ℂ)+(a-b)*(s : ℂ)) := by
    push_cast
    ring
  rw [he,norm_mul,hz,one_mul]
  calc
    _ ≤ ‖a*((r-s : ℝ) : ℂ)‖+‖(a-b)*(s : ℂ)‖ := norm_add_le _ _
    _ = |r-s|+‖a-b‖*s := by simp only [norm_mul,ha,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs0,one_mul]
    _ ≤ _ := add_le_add le_rfl ((mul_le_mul_of_nonneg_left hs1 (norm_nonneg _)).trans_eq (mul_one _))

/-- Uniform graph periods plus skew-character annihilation become genuine
simultaneous periods of the scalar phase-weighted cubic functions. -/
lemma projected_cubic_period (T : Finset G) (h0 : (0 : G) ∈ T) (F : G → AddChar G ℂ)
    (hF : LocallyAdditive (diffBall T 4 : Set G) F)
    (hdiff : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t)
    {s t : G} (hs : s ∈ T) (ht : t ∈ T) {ε e : ℝ}
    (hper : ∀ p : G × AddChar G ℂ,
      |triple (frequencyGraph T F) (p+(s,F s))-triple (frequencyGraph T F) (p+(t,F t))| ≤ ε)
    (d : G) (hskew : ‖skewPhase F (s-t) d-1‖ ≤ e) (x : G) :
    ‖cubicSmooth T (fun y ↦ skewPhase F y d) (x+s)-cubicSmooth T (fun y ↦ skewPhase F y d) (x+t)‖ ≤ ε+e := by
  rw [cubicSmooth_skew_shift T h0 F hF x d hs,cubicSmooth_skew_shift T h0 F hF x d ht]
  have hscalar := hper (x,F x)
  rw [graph_triple_shift T h0 F hF x hs,graph_triple_shift T h0 F hF x ht] at hscalar
  have hphase : ‖skewPhase F s d-skewPhase F t d‖ ≤ e := by
    have he := norm_character_difference (graphSkewCharacter F d) (s,F s) (t,F t)
    rw [graphSkewCharacter_apply,graphSkewCharacter_apply,graphSkewCharacter_difference T F hdiff hs ht] at he
    exact he.trans_le hskew
  exact (unit_scalar_difference _ _ _ (skewPhase_norm F x d) (skewPhase_norm F s d) _ _
    (triple_nonneg T _) (triple_le_one T ⟨0,h0⟩ _)).trans (add_le_add hscalar hphase)

/-- Simultaneous cubic almost-periods for all skew phases with normalized bias
at least eta. The sample and cardinality costs use |G|, not |G x dual(G)|. -/
theorem exists_skew_cubic_almost_periods (T : Finset G) (h0 : (0 : G) ∈ T)
    (F : G → AddChar G ℂ) (hF : LocallyAdditive (diffBall T 4 : Set G) F)
    (hdiff : ∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t)
    {n : ℕ} (hn : 0 < n) {η ε : ℝ} (hη : 0 < η) (hε : 0 ≤ ε)
    (hL2 : 8 ≤ (n : ℝ)*ε^2)
    (hspec : 16*(Fintype.card G : ℝ) ≤ (n : ℝ)*(T.card : ℝ)*η^4*ε^2) :
    ∃ X : Finset G, X.Nonempty ∧ X ⊆ T ∧
      T.card^n*T.card ≤ 2*(Fintype.card G)^n*X.card ∧
      (∀ s ∈ X, ∀ t ∈ X, ∀ x, |triple T (x+s)-triple T (x+t)| ≤ ε) ∧
      ∀ s ∈ X, ∀ t ∈ X, ∀ d : G, η ≤ normalizedSkewBias T F d → ∀ x,
        ‖cubicSmooth T (fun y ↦ skewPhase F y d) (x+s)-
          cubicSmooth T (fun y ↦ skewPhase F y d) (x+t)‖ ≤ 2*ε := by
  let A := frequencyGraph T F
  have hA : A.Nonempty := ⟨(0,F 0),(mem_frequencyGraph T F _).mpr ⟨h0,rfl⟩⟩
  have hcost : 16*((A-A).card : ℝ) ≤ (n : ℝ)*(A.card : ℝ)*η^4*ε^2 := by
    rw [card_frequencyGraph]
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast graph_sub_card_le T F hdiff) (by norm_num)).trans hspec
  obtain ⟨Y,hY,hsub,hsize,hper,hchar⟩ := exists_joint_spectrum_periods A hA hn hη hε hL2 hcost
  let X := Y.image Prod.fst
  have hinj : Set.InjOn Prod.fst (Y : Set (G × AddChar G ℂ)) := by
    intro a ha b hb he
    apply Prod.ext he
    rw [((mem_frequencyGraph T F a).mp (hsub ha)).2,((mem_frequencyGraph T F b).mp (hsub hb)).2,he]
  have hXcard : X.card = Y.card := card_image_of_injOn hinj
  have hXT : X ⊆ T := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
    exact ((mem_frequencyGraph T F p).mp (hsub hp)).1
  have hmem {x : G} (hx : x ∈ X) : (x,F x) ∈ Y := by
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hx
    have he : (p.1,F p.1) = p := Prod.ext rfl ((mem_frequencyGraph T F p).mp (hsub hp)).2.symm
    rwa [he]
  refine ⟨X,image_nonempty.mpr hY,hXT,?_,?_,?_⟩
  · rw [card_frequencyGraph] at hsize
    rw [hXcard]
    exact hsize.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2
      (Nat.pow_le_pow_left (graph_add_card_le T F hdiff) n)))
  · intro s hs t ht x
    have hp := hper (s,F s) (hmem hs) (t,F t) (hmem ht) (x,F x)
    rwa [graph_triple_shift T h0 F hF x (hXT hs),graph_triple_shift T h0 F hF x (hXT ht)] at hp
  · intro s hs t ht d hd x
    have hc := hchar (s,F s) (hmem hs) (t,F t) (hmem ht) (graphSkewCharacter F d)
      (by simpa only [A,graphSkewCharacter_mean,normalizedSkewBias] using hd)
    rw [graphSkewCharacter_difference T F hdiff (hXT hs) (hXT ht)] at hc
    have hp := projected_cubic_period T h0 F hF hdiff (hXT hs) (hXT ht)
      (hper _ (hmem hs) _ (hmem ht)) d hc x
    simpa only [two_mul] using hp

#print axioms exists_skew_cubic_almost_periods
end Erdos3JointGraphAlmostPeriods
