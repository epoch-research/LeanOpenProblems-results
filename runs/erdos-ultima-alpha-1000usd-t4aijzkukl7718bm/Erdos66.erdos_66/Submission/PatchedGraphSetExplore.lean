import Submission.GraphPatchExplore

/-! Actual-set finite patching after one color assignment. -/
namespace Erdos66PatchedGraphSet
open Erdos66GraphPatch Erdos66TranslatedGraphPartition
  Erdos66UniformGraphColorTransfer Erdos66AnchoredGraphColorTransfer
  Erdos66CompletePartitionColorTransfer Erdos66UniformColorMoments
  Erdos66ActualColorRootTransfer Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 2600000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {α H : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
  [AddCommGroup H] [DecidableEq H]

noncomputable def patch (f g : F → F) (T : Finset F) (x : F) : F :=
  if x∈T then g x else f x

lemma patch_on (f g : F → F) (T : Finset F) (x : F) (hx : x∈T) :
    patch f g T x=g x := by simp [patch,hx]

lemma patch_off (f g : F → F) (T : Finset F) (x : F) (hx : x∉T) :
    patch f g T x=f x := by simp [patch,hx]

lemma patched_graphSet_on {n : ℕ} (ρ : Fin n ≃ F) (B : α → Finset H)
    (ω : Fin n → α) (f g : F → F) (T : Finset F) :
    ∀ x∈T, ∀ y : F, ∀ q : H,
      (((x,y),q)∈graphSet (patch f g T) ρ B ω ↔ ((x,y),q)∈graphSet g ρ B ω) :=
  graphSet_eq_on_columns ρ B ω (patch f g T) g T (patch_on f g T)

lemma patched_graphSet_off {n : ℕ} (ρ : Fin n ≃ F) (B : α → Finset H)
    (ω : Fin n → α) (f g : F → F) (T : Finset F) :
    ∀ x, x∉T → ∀ y : F, ∀ q : H,
      (((x,y),q)∈graphSet (patch f g T) ρ B ω ↔ ((x,y),q)∈graphSet f ρ B ω) := by
  intro x hx y q
  rw [mem_graphSet,mem_graphSet]
  simp only [Prod.fst,Prod.snd,patch_off f g T x hx]

/-- The arbitrary replacement values and their columns are chosen after the
coloring. Both agreement properties and the actual pair-count estimate hold. -/
theorem exists_actual_patched_graph_budget {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2)
    (B : α → Finset H) (S : Finset H) (w : H → ℝ) (hw : ∀ q∈S, 0≤w q) :
    ∃ ω : Fin n → α, ∀ (f g : F → F) (D : ℕ), HasBoundedSums f D →
      ∀ T : Finset F,
        (∀ x∈T, ∀ y : F, ∀ q : H,
          (((x,y),q)∈graphSet (patch f g T) ρ B ω ↔ ((x,y),q)∈graphSet g ρ B ω)) ∧
        (∀ x, x∉T → ∀ y : F, ∀ q : H,
          (((x,y),q)∈graphSet (patch f g T) ρ B ω ↔ ((x,y),q)∈graphSet f ρ B ω)) ∧
        ∀ q∈S, ∀ t s : F,
          w q*((pairCount (graphSet (patch f g T) ρ B ω)
            (graphSet (patch f g T) ρ B ω) ((t,s),q):ℝ)-
            (n:ℝ)^2*kernelMean (coarseKernel B q))^2≤
            (2*(D:ℝ)^2*(n:ℝ)+32*(T.card:ℝ)^2)*kernelBudget n S (coarseKernel B) w := by
  obtain ⟨ω,hω⟩ := exists_patched_graph_budget ρ hF S (coarseKernel B)
    (fun q hq ↦ coarseKernel_symm B q) w hw
  refine ⟨ω,fun f g D hf T ↦ ⟨patched_graphSet_on ρ B ω f g T,
    patched_graphSet_off ρ B ω f g T,fun q hq t s ↦ ?_⟩⟩
  rw [graphSet_pairCount]
  exact hω f (patch f g T) D hf T (fun x hx ↦ (patch_off f g T x hx).symm) q hq t s

end Erdos66PatchedGraphSet
