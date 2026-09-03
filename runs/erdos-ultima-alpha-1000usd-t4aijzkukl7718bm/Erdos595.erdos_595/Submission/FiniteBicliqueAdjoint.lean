import Submission.ArcAdjoint
import Submission.NoetherianNeighborhoods

/-!
Finite-parameter reduction for biclique right adjoints whose base graphs
have finitely determined common neighborhoods. This does not settle the
covering question for the resulting finite-parameter graph.
-/

set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595FiniteBiclique
open Erdos595ArcAdjoint Erdos595Noetherian

variable {V : Type*}

def common (G : SimpleGraph V) (S : Set V) : Set V :=
  {w | ∀ v ∈ S, G.Adj v w}

lemma subset_common_common (G : SimpleGraph V) (S : Set V) :
    S ⊆ common G (common G S) :=
  fun v hv w hw => (hw v hv).symm

lemma common_antitone (G : SimpleGraph V) : Antitone (common G) :=
  fun _ _ h _ hw v hv => hw v (h hv)

lemma common_three (G : SimpleGraph V) (S : Set V) :
    common G (common G (common G S)) = common G S := by
  exact (common_antitone G (subset_common_common G S)).antisymm
    (subset_common_common G (common G S))

/-- A set determines a maximal ordered biclique by the common-neighbor
polarity. Empty sides are permitted. -/
def completion (G : SimpleGraph V) (S : Set V) : Biclique G :=
  ⟨(common G S, common G (common G S)), fun a ha b hb => hb a ha⟩

/-- Finite subsets are parameters for these completed bicliques. -/
def finiteRight (G : SimpleGraph V) : SimpleGraph (Finset V) :=
  (right G).comap (fun S : Finset V => completion G S)

def finiteToRight (G : SimpleGraph V) : finiteRight G →g right G where
  toFun S := completion G S
  map_rel' h := h

lemma exists_finite_common (G : SimpleGraph V) (hG : FiniteCommonNeighbors G)
    (S : Set V) : ∃ t : Finset V, common G t = common G S := by
  classical
  obtain ⟨t, ht⟩ := hG S
  refine ⟨t.image Subtype.val, ?_⟩
  ext w
  simp only [common, mem_setOf_eq, Finset.mem_coe, Finset.mem_image]
  constructor
  · intro h
    apply (ht w).mp
    intro v hv
    exact h v ⟨v, hv, rfl⟩
  · intro h v hv
    obtain ⟨u, hu, rfl⟩ := hv
    exact h u u.2

/-- A biclique can be enlarged to a completed biclique with finite
parameters, provided common neighborhoods are finitely determined. -/
theorem finite_completion_dominates (G : SimpleGraph V)
    (hG : FiniteCommonNeighbors G) (p : Biclique G) :
    ∃ S : Finset V, p.1.1 ⊆ (completion G S).1.1 ∧
      p.1.2 ⊆ (completion G S).1.2 := by
  obtain ⟨S, hS⟩ := exists_finite_common G hG p.1.2
  refine ⟨S, ?_, ?_⟩
  · change p.1.1 ⊆ common G S
    rw [hS]
    exact fun a ha b hb => (p.2 a ha b hb).symm
  · change p.1.2 ⊆ common G (common G S)
    rw [hS]
    exact subset_common_common G p.1.2

noncomputable def rightToFinite (G : SimpleGraph V)
    (hG : FiniteCommonNeighbors G) : right G →g finiteRight G where
  toFun p := (finite_completion_dominates G hG p).choose
  map_rel' := by
    intro p q hpq
    have hp := (finite_completion_dominates G hG p).choose_spec
    have hq := (finite_completion_dominates G hG q).choose_spec
    change Set.Nonempty (_ ∩ _) ∧ Set.Nonempty (_ ∩ _)
    obtain ⟨a, hap, haq⟩ := hpq.1
    obtain ⟨b, hbq, hbp⟩ := hpq.2
    exact ⟨⟨a, hp.2 hap, hq.1 haq⟩, ⟨b, hq.2 hbq, hp.1 hbp⟩⟩

/-- The finite-parameter graph and full right adjoint have equivalent
countable triangle-free coverability. -/
theorem cover_iff (G : SimpleGraph V) (hG : FiniteCommonNeighbors G) :
    Erdos595Work.IsCountableUnionOfTriangleFree (right G) ↔
      Erdos595Work.IsCountableUnionOfTriangleFree (finiteRight G) :=
  ⟨Erdos595Work.countable_union_of_hom (finiteToRight G),
    Erdos595Work.countable_union_of_hom (rightToFinite G hG)⟩

theorem shift_cover_iff (A : Type*) [LinearOrder A] :
    Erdos595Work.IsCountableUnionOfTriangleFree
        (right (Erdos595MiddleCorner.graph A)) ↔
      Erdos595Work.IsCountableUnionOfTriangleFree
        (finiteRight (Erdos595MiddleCorner.graph A)) :=
  cover_iff _ (shift_finiteCommonNeighbors A)

#print axioms finite_completion_dominates
#print axioms rightToFinite
#print axioms cover_iff
#print axioms shift_cover_iff
end Erdos595FiniteBiclique
