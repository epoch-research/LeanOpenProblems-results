import Submission.UniformLocalQuadraticInverse

/-! Retaining the full polynomial-density derivative set by using its fourfold
difference domain, rather than prematurely restricting it to a Bohr translate. -/
namespace Erdos3UnlocalizedBilinearExtraction
open Finset Erdos3FiniteUniformity Erdos3FiniteFourier Erdos3HigherFreimanExtraction
  Erdos3HigherFreimanRestriction Erdos3LocalFreimanExtension Erdos3LocalQuadraticIntegration
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def diffBall (T : Finset G) (n : ℕ) : Finset G := n • (T-T)

lemma diffBall_eq (T : Finset G) (n : ℕ) : diffBall T n = n • T-n • T := by
  simp only [diffBall,sub_eq_add_neg,nsmul_add,neg_nsmul]

lemma diffBall_mono (T : Finset G) (hT : T.Nonempty) {m n : ℕ} (hmn : m ≤ n) :
    diffBall T m ⊆ diffBall T n := by
  obtain ⟨t,ht⟩ := hT
  have hz : (0 : G) ∈ T-T := by simpa only [sub_self] using sub_mem_sub ht ht
  exact nsmul_subset_nsmul_right hz hmn

lemma mem_diffBall_one {T : Finset G} {x : G} : x ∈ diffBall T 1 ↔ x ∈ T-T := by
  simp only [diffBall,one_nsmul]

lemma diffBall_add {T : Finset G} {m n : ℕ} {x y : G}
    (hx : x ∈ diffBall T m) (hy : y ∈ diffBall T n) : x+y ∈ diffBall T (m+n) := by
  simpa only [diffBall,add_nsmul] using add_mem_add hx hy

lemma diffBall_neg {T : Finset G} {n : ℕ} {x : G} (hx : x ∈ diffBall T n) :
    -x ∈ diffBall T n := by
  rw [diffBall_eq] at hx ⊢
  obtain ⟨a,ha,b,hb,rfl⟩ := mem_sub.mp hx
  simpa only [neg_sub] using sub_mem_sub hb ha

lemma diffBall_sub {T : Finset G} {m n : ℕ} {x y : G}
    (hx : x ∈ diffBall T m) (hy : y ∈ diffBall T n) : x-y ∈ diffBall T (m+n) := by
  simpa only [sub_eq_add_neg] using diffBall_add hx (diffBall_neg hy)

lemma subset_diffBall_one (T : Finset G) (h0 : (0 : G) ∈ T) : T ⊆ diffBall T 1 := by
  intro x hx
  rw [mem_diffBall_one]
  simpa only [sub_zero] using sub_mem_sub hx h0

lemma recenter_difference (H : Finset G) (a : G) :
    (H.image (fun h ↦ h-a))-(H.image (fun h ↦ h-a)) = H-H := by
  ext x
  constructor
  · intro hx
    obtain ⟨u,hu,v,hv,rfl⟩ := mem_sub.mp hx
    obtain ⟨h,hh,rfl⟩ := mem_image.mp hu
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hv
    simpa only [show (h-a)-(k-a) = h-k by abel] using sub_mem_sub hh hk
  · intro hx
    obtain ⟨h,hh,k,hk,rfl⟩ := mem_sub.mp hx
    exact mem_sub.mpr ⟨h-a,mem_image.mpr ⟨h,hh,rfl⟩,k-a,mem_image.mpr ⟨k,hk,rfl⟩,by abel⟩

noncomputable def unlocalizedLoss (δ : ℝ) : ℝ :=
  (2*(((2 : ℝ)^65/δ^41)^25+1))^388

/-- A twelve-Freiman restriction retains polynomial density and supports all
the local additions needed for symmetry. No Bohr localization loss occurs here. -/
theorem large_U3_unlocalized_bilinear (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) (hU : δ ≤ uniformityPower 2 f) :
    ∃ T : Finset G, ∃ F : G → AddChar G ℂ, ∃ a₀ : G, ∃ χ₀ : AddChar G ℂ,
      0 ∈ T ∧ δ^5/256*(Fintype.card G : ℝ) ≤ unlocalizedLoss δ*(T.card : ℝ) ∧
      F 0 = 0 ∧ LocallyAdditive (diffBall T 4 : Set G) F ∧
      (∀ s ∈ T, ∀ t ∈ T, F (s-t) = F s-F t) ∧
      (∀ t ∈ T, δ/2 ≤ ‖hat (derivative f (t+a₀)) (F t+χ₀)‖^2) := by
  obtain ⟨H,ξ,hH,hFreiman,hcoef,hsize⟩ := large_U3_higher_freiman_graph 12 (by decide) f hf hδ hU
  change δ^5/256*(Fintype.card G : ℝ) ≤ unlocalizedLoss δ*(H.card : ℝ) at hsize
  obtain ⟨F,hF0,hFdiff,hFadd⟩ := exists_local_additive_extension H 4 (by decide) ξ hFreiman
  obtain ⟨a₀,ha₀⟩ := hH
  let T := H.image (fun h ↦ h-a₀)
  have hTc : T.card = H.card := card_image_of_injective _ (fun _ _ h ↦ sub_left_injective h)
  have hP : diffBall T 4 = (4 : ℕ) • H-(4 : ℕ) • H := by
    rw [diffBall,recenter_difference,← diffBall,diffBall_eq]
  refine ⟨T,F,a₀,ξ a₀,mem_image.mpr ⟨a₀,ha₀,sub_self _⟩,?_,hF0,?_,?_,?_⟩
  · rwa [hTc]
  · intro x hx y hy hxy
    rw [hP] at hx hy hxy
    exact hFadd x hx y hy hxy
  · intro s hs t ht
    obtain ⟨h,hh,rfl⟩ := mem_image.mp hs
    obtain ⟨k,hk,rfl⟩ := mem_image.mp ht
    rw [show (h-a₀)-(k-a₀) = h-k by abel,hFdiff h hh k hk,
      hFdiff h hh a₀ ha₀,hFdiff k hk a₀ ha₀]
    abel
  · intro t ht
    obtain ⟨h,hh,rfl⟩ := mem_image.mp ht
    rw [hFdiff h hh a₀ ha₀,sub_add_cancel,sub_add_cancel]
    exact hcoef h hh

#print axioms large_U3_unlocalized_bilinear
end Erdos3UnlocalizedBilinearExtraction
