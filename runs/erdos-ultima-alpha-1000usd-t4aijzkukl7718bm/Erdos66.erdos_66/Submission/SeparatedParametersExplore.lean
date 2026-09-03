import Submission.GridBandPartitionExplore

/-! Choosing finitely many mutually nonopposite unused parabola parameters. -/
namespace Erdos66SeparatedParameters
open Erdos66ParabolaRepair
open scoped Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma exists_separated_finset (hF : ringChar F ≠ 2) (U : Finset F) (L : ℕ)
    (hsize : 2*(U.card+L)+1 < Fintype.card F) :
    ∃ W : Finset F, W.card=L ∧ (∀ w∈W, w ≠ 0 ∧ w∉U ∧ -w∉U) ∧
      ∀ u∈W, ∀ v∈W, u+v ≠ 0 := by
  induction L with
  | zero => exact ⟨∅,by simp,by simp,by simp⟩
  | succ L ih =>
    obtain ⟨W,hcard,hW,hopp⟩ := ih (by omega)
    have hUW : 2*(U ∪ W).card+1 < Fintype.card F := by
      have hh := Finset.card_union_le U W
      omega
    obtain ⟨w,hw0,hw,hnw⟩ := exists_unused_parameter (U ∪ W) hUW
    have hwU : w∉U := fun hh ↦ hw (Finset.mem_union_left _ hh)
    have hwW : w∉W := fun hh ↦ hw (Finset.mem_union_right _ hh)
    have hnwU : -w∉U := fun hh ↦ hnw (Finset.mem_union_left _ hh)
    have hnwW : -w∉W := fun hh ↦ hnw (Finset.mem_union_right _ hh)
    refine ⟨insert w W,by simp [hwW,hcard],?_,?_⟩
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨hw0,hwU,hnwU⟩
      · exact hW v hv
    · intro u hu v hv
      by_cases hu0 : u=w
      · subst u
        by_cases hv0 : v=w
        · subst v
          intro hh
          exact parameter_ne_neg hF hw0 (by linear_combination hh)
        · have hvW := (Finset.mem_insert.mp hv).resolve_left hv0
          intro hh
          exact hnwW ((show v=-w by linear_combination hh) ▸ hvW)
      · have huW := (Finset.mem_insert.mp hu).resolve_left hu0
        by_cases hv0 : v=w
        · subst v
          intro hh
          exact hnwW ((show u=-w by linear_combination hh) ▸ huW)
        · exact hopp u huW v ((Finset.mem_insert.mp hv).resolve_left hv0)

/-- The size threshold is linear in the number of new parameters. -/
theorem exists_separated_parameters (hF : ringChar F ≠ 2) (U : Finset F) (L : ℕ)
    (hsize : 2*(U.card+L)+1 < Fintype.card F) :
    ∃ w : Fin L → F, Function.Injective w ∧ (∀ i, w i ≠ 0) ∧
      (∀ i, w i∉U ∧ -(w i)∉U) ∧ ∀ i j, w i+w j ≠ 0 := by
  obtain ⟨W,hcard,hW,hopp⟩ := exists_separated_finset hF U L hsize
  let e : Fin L ≃ W := (Fintype.equivFinOfCardEq (by simpa using hcard)).symm
  let w := fun i ↦ (e i).val
  refine ⟨w,?_,fun i ↦ (hW _ (e i).property).1,
    fun i ↦ (hW _ (e i).property).2,fun i j ↦ hopp _ (e i).property _ (e j).property⟩
  intro i j hij
  exact e.injective (Subtype.ext hij)

end Erdos66SeparatedParameters
