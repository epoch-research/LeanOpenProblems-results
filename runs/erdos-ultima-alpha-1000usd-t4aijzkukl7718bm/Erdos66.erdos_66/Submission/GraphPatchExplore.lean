import Submission.HistogramPatchExplore

/-! A finite patch changes only two reflected sets of pair-sum inputs.
The resulting bound is additive in the patch energy, rather than multiplying
its cost by the full field cardinality. This is still a finite-group result. -/
namespace Erdos66GraphPatch
open Erdos66HistogramPatch Erdos66TranslatedGraphPartition
  Erdos66UniformGraphColorTransfer Erdos66FiberColorEnergy
  Erdos66UniformColorMoments Erdos66FixedPatternColorEnergy
  Erdos66CompletePartitionColorTransfer
open scoped Classical
set_option maxHeartbeats 2400000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def pairMap (f : F → F) (t s : F) (x : F) : F :=
  s-(f x+f (t-x))

lemma sumCoeff_histogram (f : F → F) (q t s : F) :
    histogram (pairMap f t s) q=(sumCoeff f q t s:ℝ) := by
  have hrel (x : F) : pairMap f t s x=q ↔ f x+f (t-x)=s-q := by
    unfold pairMap
    constructor <;> intro he <;> linear_combination -he
  unfold histogram
  simp_rw [hrel]
  rw [←Finset.sum_filter]
  simp [sumCoeff,Fintype.card_subtype]

noncomputable def reflectedPatch (T : Finset F) (t : F) : Finset F :=
  T ∪ T.image (fun x ↦ t-x)

lemma reflectedPatch_card (T : Finset F) (t : F) : (reflectedPatch T t).card≤2*T.card := by
  exact (Finset.card_union_le _ _).trans (by
    have := Finset.card_image_le (s := T) (f := fun x ↦ t-x)
    omega)

lemma pairMap_eq_off_patch (f g : F → F) (T : Finset F)
    (hfg : ∀ x, x∉T → f x=g x) (t s x : F) (hx : x∉reflectedPatch T t) :
    pairMap f t s x=pairMap g t s x := by
  have hxT : x∉T := fun h ↦ hx (Finset.mem_union_left _ h)
  have hyT : t-x∉T := by
    intro h
    apply hx
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨t-x,h,by simp⟩
  simp only [pairMap,hfg x hxT,hfg (t-x) hyT]

lemma sumCoeff_patch_L1 (f g : F → F) (T : Finset F)
    (hfg : ∀ x, x∉T → f x=g x) (t s : F) :
    (∑ q : F, |(sumCoeff f q t s:ℝ)-(sumCoeff g q t s:ℝ)|)≤4*(T.card:ℝ) := by
  simp_rw [←sumCoeff_histogram]
  have he := histogram_change_L1 (pairMap f t s) (pairMap g t s) (reflectedPatch T t)
    (pairMap_eq_off_patch f g T hfg t s)
  have hc : ((reflectedPatch T t).card:ℝ)≤2*(T.card:ℝ) := by
    exact_mod_cast reflectedPatch_card T t
  linarith

lemma sumCoeff_patch_L2 (f g : F → F) (T : Finset F)
    (hfg : ∀ x, x∉T → f x=g x) (t s : F) :
    (∑ q : F, ((sumCoeff f q t s:ℝ)-(sumCoeff g q t s:ℝ))^2)≤16*(T.card:ℝ)^2 := by
  simp_rw [←sumCoeff_histogram]
  have he := histogram_change_L2 (pairMap f t s) (pairMap g t s) (reflectedPatch T t)
    (pairMap_eq_off_patch f g T hfg t s)
  have hc : ((reflectedPatch T t).card:ℝ)≤2*(T.card:ℝ) := by
    exact_mod_cast reflectedPatch_card T t
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (reflectedPatch T t).card) hc 2
  nlinarith only [he,hs]

lemma graphSum_patch_sq (f g : F → F) (T : Finset F)
    (hfg : ∀ x, x∉T → f x=g x) {n : ℕ} (ρ : Fin n ≃ F)
    (V : Fin n → Fin n → ℝ) (t s : F) :
    (graphSum f ρ V t s-graphSum g ρ V t s)^2≤
      16*(T.card:ℝ)^2*energy n (fun i j ↦ ρ i+ρ j) V := by
  rw [graphSum_fibers,graphSum_fibers,←Finset.sum_sub_distrib]
  simp_rw [←mul_sub]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fiber n (fun i j ↦ ρ i+ρ j) V)
    (fun q ↦ (sumCoeff f q t s:ℝ)-(sumCoeff g q t s:ℝ))
  have hmul := mul_le_mul_of_nonneg_left (sumCoeff_patch_L2 f g T hfg t s)
    (show 0≤energy n (fun i j ↦ ρ i+ρ j) V from Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  change _≤energy n (fun i j ↦ ρ i+ρ j) V*_ at hcs
  exact hcs.trans (by nlinarith only [hmul])

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α]

/-- The patched graph need not satisfy an a priori degree or fiber bound. -/
theorem patched_graph_error_sq (f g : F → F) (D : ℕ) (hf : HasBoundedSums f D)
    (T : Finset F) (hfg : ∀ x, x∉T → f x=g x) {n : ℕ} (ρ : Fin n ≃ F)
    (K : α → α → ℝ) (ω : Fin n → α) (t s : F) :
    (graphSum g ρ (fun i j ↦ K (ω i) (ω j)) t s-(n:ℝ)^2*kernelMean K)^2≤
      (2*(D:ℝ)^2*(n:ℝ)+32*(T.card:ℝ)^2)*colorEnergy ρ K ω := by
  have hbase := graphSum_error_sq f ρ D hf K ω t s
  have hpatch := graphSum_patch_sq f g T hfg ρ (fun i j ↦ centeredKernel K (ω i) (ω j)) t s
  rw [graphSum_centered,graphSum_centered] at hpatch
  change _≤16*(T.card:ℝ)^2*colorEnergy ρ K ω at hpatch
  nlinarith [sq_nonneg
    ((graphSum f ρ (fun i j ↦ K (ω i) (ω j)) t s-(n:ℝ)^2*kernelMean K)+
     (graphSum f ρ (fun i j ↦ K (ω i) (ω j)) t s-
      graphSum g ρ (fun i j ↦ K (ω i) (ω j)) t s))]

/-- One coloring precedes every later base graph and arbitrary finite patch. -/
theorem exists_patched_graph_budget {ι : Type*} {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2)
    (S : Finset ι) (K : ι → α → α → ℝ) (hK : ∀ k∈S, ∀ x y, K k x y=K k y x)
    (w : ι → ℝ) (hw : ∀ k∈S, 0≤w k) :
    ∃ ω : Fin n → α, ∀ (f g : F → F) (D : ℕ), HasBoundedSums f D →
      ∀ T : Finset F, (∀ x, x∉T → f x=g x) → ∀ k∈S, ∀ t s : F,
        w k*(graphSum g ρ (fun i j ↦ K k (ω i) (ω j)) t s-(n:ℝ)^2*kernelMean (K k))^2≤
          (2*(D:ℝ)^2*(n:ℝ)+32*(T.card:ℝ)^2)*kernelBudget n S K w := by
  obtain ⟨ω,hω⟩ := exists_energy_budget ρ hF S K hK w hw
  refine ⟨ω,fun f g D hf T hfg k hk t s ↦ ?_⟩
  have he := mul_le_mul_of_nonneg_left (patched_graph_error_sq f g D hf T hfg ρ (K k) ω t s) (hw k hk)
  have he' := mul_le_mul_of_nonneg_left (hω k hk)
    (show (0:ℝ)≤2*(D:ℝ)^2*(n:ℝ)+32*(T.card:ℝ)^2 by positivity)
  nlinarith only [he,he']

end Erdos66GraphPatch
