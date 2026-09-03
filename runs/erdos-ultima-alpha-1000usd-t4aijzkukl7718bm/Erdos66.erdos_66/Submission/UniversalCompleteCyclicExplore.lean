import Submission.UniversalCompleteAccuracyExplore
import Submission.DisjointBlockOperatorExplore

/-! A complete graph partition, transported through two-coordinate thickening.
The modulus remains fixed; this does not provide a changing-scale construction. -/
namespace Erdos66UniversalCompleteCyclic
open Erdos66OriginRepair Erdos66TranslatedGraphPartition Erdos66DisjointPaletteAssembly
  Erdos66DisjointBlockOperator Erdos66CompleteKernelBasis Erdos66UniformColorMoments
  Erdos66UniversalCompleteAccuracy Erdos66CyclicThickening Erdos66MixedCyclicThickening
  Erdos66OuterCarryProfile
open scoped Classical
set_option maxHeartbeats 2800000
variable {F α : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Fintype α] [Nonempty α] [DecidableEq α]

noncomputable def graphColor {n : ℕ} (f : F → F) (ρ : Fin n ≃ F)
    (ω : Fin n → α) (z : F×F) : α := ω (ρ.symm (z.2-f z.1))

noncomputable def colorClass {n : ℕ} (f : F → F) (ρ : Fin n ≃ F)
    (ω : Fin n → α) (a : α) : Finset (F×F) :=
  Finset.univ.filter (fun z ↦ graphColor f ρ ω z=a)

omit [DecidableEq F] [Fintype α] [Nonempty α] in
lemma mem_colorClass {n : ℕ} (f : F → F) (ρ : Fin n ≃ F)
    (ω : Fin n → α) (a : α) (z : F×F) :
    z∈colorClass f ρ ω a ↔ graphColor f ρ ω z=a := by simp [colorClass]

lemma colorClass_disjoint {n : ℕ} (f : F → F) (ρ : Fin n ≃ F) (ω : Fin n → α) :
    Pairwise (fun a b ↦ Disjoint (colorClass f ρ ω a) (colorClass f ρ ω b)) := by
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  exact hab ((mem_colorClass f ρ ω a z).mp hz |>.symm.trans
    ((mem_colorClass f ρ ω b z).mp hz'))

lemma colorClass_cover {n : ℕ} (f : F → F) (ρ : Fin n ≃ F) (ω : Fin n → α) :
    Finset.univ.biUnion (colorClass f ρ ω)=Finset.univ := by
  ext z
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,mem_colorClass,iff_true]
  exact ⟨graphColor f ρ ω z,rfl⟩

lemma colorClass_eq_union {n : ℕ} (f : F → F) (ρ : Fin n ≃ F)
    (ω : Fin n → α) (a : α) :
    colorClass f ρ ω a=(Finset.univ.filter (fun i ↦ ω i=a)).biUnion
      (fun i ↦ graphSlice f (ρ i)) := by
  ext z
  simp only [mem_colorClass,Finset.mem_biUnion,Finset.mem_filter,Finset.mem_univ,
    true_and,mem_graphSlice,graphColor]
  constructor
  · intro hz
    refine ⟨ρ.symm (z.2-f z.1),hz,?_⟩
    rw [ρ.apply_symm_apply]
    ring
  · rintro ⟨i,hi,hz⟩
    have he : ρ.symm (z.2-f z.1)=i := by
      apply ρ.injective
      rw [ρ.apply_symm_apply,hz]
      ring
    rwa [he]

lemma colorClass_pairCount {n : ℕ} (f : F → F) (ρ : Fin n ≃ F)
    (ω : Fin n → α) (a b : α) (t s : F) :
    (pairCount (colorClass f ρ ω a) (colorClass f ρ ω b) (t,s):ℝ)=
      graphSum f ρ (fun i j ↦ mask (a,b) (ω i) (ω j)) t s := by
  rw [colorClass_eq_union,colorClass_eq_union,selected_union_count _
    (fun i j hij ↦ graphSlice_disjoint f (fun he ↦ hij (ρ.injective he)))]
  simp_rw [graphSlice_pairCount]
  push_cast
  simp only [graphSum,mask,Prod.mk.injEq,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hia : ω i=a
  · simp only [hia,true_and,if_true]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp
  · simp [hia]

/-- Complete disjoint plane colors, selected before all later graphs and
accuracy requests. The explicit fourth power in the alphabet is retained. -/
theorem exists_complete_plane_colors {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2) :
    ∃ ω : Fin n → α, ∀ (f : F → F) (D : ℕ), HasBoundedSums f D →
      ∀ ε : ℝ, 0≤ε → 10*(D:ℝ)^2*(Fintype.card α:ℝ)^4≤ε^2*n →
      ∀ a b : α, ∀ t s : F,
        |(pairCount (colorClass f ρ ω a) (colorClass f ρ ω b) (t,s):ℝ)-
          (n:ℝ)^2/(Fintype.card α:ℝ)^2|≤ε*((n:ℝ)^2/(Fintype.card α:ℝ)^2) := by
  obtain ⟨ω,hω⟩ := exists_universal_graph_accuracy (α := α) ρ hF
  refine ⟨ω,fun f D hf ε hε hsize a b t s ↦ ?_⟩
  have hm (x y : α) : 0 ≤ mask (a,b) x y := by unfold mask; split_ifs <;> norm_num
  have he := hω f D hf ε hε hsize (mask (a,b)) hm t s
  rw [←colorClass_pairCount,mask_mean] at he
  simpa only [Fintype.card_prod,Nat.cast_mul,div_eq_mul_inv,pow_two,mul_one,one_mul,mul_assoc] using he

variable (p K : ℕ) [NeZero p] [NeZero K]

lemma thickened_disjoint {B C : Finset (ZMod p×ZMod p)} (h : Disjoint B C) :
    Disjoint (thickenedSet p K B) (thickenedSet p K C) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  simp only [thickenedSet,Finset.mem_filter,Finset.mem_univ,true_and] at hz hz'
  exact Finset.disjoint_left.mp h hz hz'

lemma thickened_cover {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset (ZMod p×ZMod p)) (hP : Finset.univ.biUnion P=Finset.univ) :
    Finset.univ.biUnion (fun a ↦ thickenedSet p K (P a))=Finset.univ := by
  ext z
  simp only [Finset.mem_univ,iff_true]
  let xy := (cyclicDigitEquiv (p*K)).symm z
  have hz : (reduceDigit p K xy.1,reduceDigit p K xy.2)∈Finset.univ.biUnion P := by
    rw [hP]; exact Finset.mem_univ _
  obtain ⟨a,ha,hz⟩ := Finset.mem_biUnion.mp hz
  exact Finset.mem_biUnion.mpr ⟨a,ha,by
    simpa only [thickenedSet,Finset.mem_filter,Finset.mem_univ,true_and,xy] using hz⟩

end Erdos66UniversalCompleteCyclic
