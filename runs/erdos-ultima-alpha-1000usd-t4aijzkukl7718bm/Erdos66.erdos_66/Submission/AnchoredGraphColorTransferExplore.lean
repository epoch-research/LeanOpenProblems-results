import Submission.BoundedGraphInterpolationExplore

/-! Finite-column anchoring after color selection. The sum-fiber/degree
cost grows with the prescribed column set; it is not a uniform extension
principle for infinite prefixes. -/
namespace Erdos66AnchoredGraphColorTransfer
open Erdos66TranslatedGraphPartition Erdos66UniformGraphColorTransfer
  Erdos66BoundedGraphInterpolation Erdos66UniformColorMoments
  Erdos66CompletePartitionColorTransfer Erdos66ActualColorRootTransfer Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 2600000

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {α H : Type*} [Fintype α] [Nonempty α] [DecidableEq α]
  [AddCommGroup H] [DecidableEq H]

lemma graphSet_eq_on_columns {n : ℕ} (ρ : Fin n ≃ F) (B : α → Finset H) (ω : Fin n → α)
    (f g : F → F) (T : Finset F) (hfg : ∀ x∈T, f x=g x) :
    ∀ x∈T, ∀ y : F, ∀ q : H,
      (((x,y),q)∈graphSet f ρ B ω ↔ ((x,y),q)∈graphSet g ρ B ω) := by
  intro x hx y q
  rw [mem_graphSet,mem_graphSet]
  dsimp only [Prod.fst,Prod.snd]
  rw [hfg x hx]

/-- The same color assignment precedes all later finite prescribed graph
data. The chosen interpolant preserves those complete columns and obeys
an all-fine-target bound with explicit quadratic dependence on |T|+1. -/
theorem exists_later_anchored_graph {n : ℕ} (ρ : Fin n ≃ F) (hF : ringChar F≠2)
    (B : α → Finset H) (S : Finset H) (w : H → ℝ) (hw : ∀ q∈S, 0≤w q) :
    ∃ ω : Fin n → α, ∀ (T : Finset F) (g : F → F),
      ∃ P : Polynomial F, P.Monic ∧ P.natDegree=2*(T.card+1) ∧
        (∀ x∈T, P.eval x=g x) ∧
        (∀ x∈T, ∀ y : F, ∀ q : H,
          (((x,y),q)∈graphSet (fun z ↦ P.eval z) ρ B ω ↔ ((x,y),q)∈graphSet g ρ B ω)) ∧
        ∀ q∈S, ∀ t s : F,
          w q*((pairCount (graphSet (fun z ↦ P.eval z) ρ B ω)
            (graphSet (fun z ↦ P.eval z) ρ B ω) ((t,s),q):ℝ)-
            (n:ℝ)^2*kernelMean (coarseKernel B q))^2≤
          (2*((T.card:ℝ)+1))^2*(n:ℝ)*kernelBudget n S (coarseKernel B) w := by
  obtain ⟨ω,hω⟩ := exists_actual_uniform_graph_budget ρ hF B S w hw
  refine ⟨ω,fun T g ↦ ?_⟩
  obtain ⟨P,hP,hdeg,hPg,hbound⟩ := exists_bounded_interpolant hF T g
  refine ⟨P,hP,hdeg,hPg,graphSet_eq_on_columns ρ B ω (fun z ↦ P.eval z) g T hPg,?_⟩
  intro q hq t s
  have he := hω (fun z ↦ P.eval z) (2*(T.card+1)) hbound q hq t s
  simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one] using he

/-- A reflected set of constant prescribed values forces a sum fiber of
at least that size. No graph choice can make this cost independent of T. -/
theorem constant_prescription_requires_budget (f : F → F) (D : ℕ) (hf : HasBoundedSums f D)
    (T : Finset F) (t c : F) (hT : ∀ x∈T, t-x∈T) (hc : ∀ x∈T, f x=c) : T.card≤D := by
  have hbound := hf t (c+c)
  rw [Fintype.card_subtype] at hbound
  apply le_trans (Finset.card_le_card ?_) hbound
  intro x hx
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ x,by rw [hc x hx,hc (t-x) (hT x hx)]⟩

end Erdos66AnchoredGraphColorTransfer
