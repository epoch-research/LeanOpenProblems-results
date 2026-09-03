import Submission.ContractionBaseData

/-! Exact integral and fractional counts for the contraction obstruction.
This is not a disproof of Erdős 184. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.ContractionGap
open Critical Rigidity BlockRestriction CycleCertificates
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

abbrev BaseVertexAt (z : Fin 15) := {v : Fin 15 // v ≠ z}

def restore (z : Fin 15) : Option (BaseVertexAt z) → Fin 15
  | none => z
  | some w => w.val

def completed (z : Fin 15) : SimpleGraph (Option (BaseVertexAt z)) :=
  ThreeCycleObstruction.exampleGraph.comap (restore z)
instance (z : Fin 15) : DecidableRel (completed z).Adj := by
  unfold completed
  infer_instance

noncomputable def completedIso (z : Fin 15) : completed z ≃g ThreeCycleObstruction.exampleGraph where
  toEquiv := Equiv.optionSubtypeNe z
  map_rel_iff' := by intro x y; cases x <;> cases y <;> rfl

lemma completed_number (z : Fin 15) : number (completed z) = 3 :=
  (number_eq_of_iso (completedIso z)).trans EvenFractionalBase.number_eq_three

lemma completed_degree (z : Fin 15) : (completed z).degree none = 4 := by
  have h := (completedIso z).degree_eq none
  have hr := ThreeCycleObstruction.exampleGraph_regular z
  simpa only [completedIso,Equiv.optionSubtypeNe_none,
    ← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using h.symm.trans hr

lemma completed_gap (z : Fin 15) : (completed z).degree none < 2 * number (completed z) := by
  rw [completed_degree,completed_number]
  decide +kernel

def leftMap (x : Fin 15) : Fin 29 := ⟨x.val,by omega⟩
def rightMap : Fin 15 → Fin 29 := ![1,15,16,17,18,19,20,21,22,23,24,25,26,27,28]

def leftEmb : BaseVertexAt 1 ↪ Fin 29 where
  toFun x := leftMap x.val
  inj' := by
    intro x y h
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun z : Fin 29 => z.val) h

def rightEmb : BaseVertexAt 0 ↪ Fin 29 where
  toFun x := rightMap x.val
  inj' := by
    have hi : Function.Injective rightMap := by decide +kernel
    intro x y h
    exact Subtype.ext (hi h)

def leftOuter (x : BaseVertexAt 1) : Fin 29 := if x.val = 0 then 15 else 1
def rightOuter (x : BaseVertexAt 0) : Fin 29 := if x.val = 1 then 0 else 1

lemma left_outside : ∀ x, leftOuter x ∉ Set.range leftEmb := by decide +kernel
lemma right_outside : ∀ x, rightOuter x ∉ Set.range rightEmb := by decide +kernel
lemma left_internal : ∀ x y, graph.Adj (leftEmb x) (leftEmb y) ↔
    (completed 1).Adj (some x) (some y) := by decide +kernel
lemma right_internal : ∀ x y, graph.Adj (rightEmb x) (rightEmb y) ↔
    (completed 0).Adj (some x) (some y) := by decide +kernel
lemma left_boundary : ∀ x v, v ∉ Set.range leftEmb →
    (graph.Adj (leftEmb x) v ↔ v = leftOuter x ∧ (completed 1).Adj (some x) none) := by decide +kernel
lemma right_boundary : ∀ x v, v ∉ Set.range rightEmb →
    (graph.Adj (rightEmb x) v ↔ v = rightOuter x ∧ (completed 0).Adj (some x) none) := by decide +kernel

noncomputable def leftModel : BlockModel graph (completed 1) where
  emb := leftEmb
  outer := leftOuter
  outside := left_outside
  internal := left_internal
  boundary := left_boundary
noncomputable def rightModel : BlockModel graph (completed 0) where
  emb := rightEmb
  outer := rightOuter
  outside := right_outside
  internal := right_internal
  boundary := right_boundary

lemma blocks_disjoint : Disjoint (Set.range leftEmb) (Set.range rightEmb) := by
  rw [Set.disjoint_left]
  decide +kernel
lemma blocks_avoid_one : (1 : Fin 29) ∉ Set.range leftEmb ∧ (1 : Fin 29) ∉ Set.range rightEmb := by decide +kernel


end Erdos184Work.ContractionGap
