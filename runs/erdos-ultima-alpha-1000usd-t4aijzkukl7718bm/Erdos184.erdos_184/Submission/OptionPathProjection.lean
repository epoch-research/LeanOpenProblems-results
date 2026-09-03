import Submission.PruneLeafPaths

/-! Projecting path families from an embedded graph with an extra isolated
vertex. The projection is injective on every path's support. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.OddPaths
set_option maxHeartbeats 1200000
variable {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V)

noncomputable def optionBase : SimpleGraph (Option V) := G.map ⟨some,Option.some_injective V⟩

lemma optionBase_adj {a b : Option V} : (optionBase G).Adj a b ↔
    ∃ x y, G.Adj x y ∧ some x = a ∧ some y = b := by
  exact SimpleGraph.map_adj _ _ _ _

noncomputable def optionProject : optionBase G →g G where
  toFun := fun x => x.getD v
  map_rel' := by
    intro a b hab
    obtain ⟨x,y,hxy,rfl,rfl⟩ := optionBase_adj G |>.mp hab
    exact hxy

lemma option_none_not_support : (none : Option V) ∉ (optionBase G).support := by
  rintro ⟨a,ha⟩
  obtain ⟨x,y,hxy,hx,hy⟩ := optionBase_adj G |>.mp ha
  cases hx

lemma option_piece_avoids (p : Piece (optionBase G)) : none ∉ p.walk.support :=
  CertificateStructure.no_isolated_on_nonempty_walk p.walk
    (p.walk.not_nil_of_ne p.ne) (option_none_not_support G)

lemma option_getD_eq {x : Option V} (hx : x ≠ none) : some (x.getD v) = x := by
  cases x with
  | none => exact (hx rfl).elim
  | some x => rfl

noncomputable def projectOptionPiece (p : Piece (optionBase G)) : Piece G where
  src := (optionProject G v) p.src
  dst := (optionProject G v) p.dst
  walk := p.walk.map (optionProject G v)
  isPath := by
    apply Walk.IsPath.mk'
    rw [Walk.support_map]
    apply (List.nodup_map_iff_inj_on p.isPath.support_nodup).mpr
    intro x hx y hy hxy
    have hxn : x ≠ none := fun h => option_piece_avoids G p (h ▸ hx)
    have hyn : y ≠ none := fun h => option_piece_avoids G p (h ▸ hy)
    exact (option_getD_eq v hxn).symm.trans ((congrArg some hxy).trans (option_getD_eq v hyn))
  ne := by
    intro h
    apply p.ne
    have hsn : p.src ≠ none := fun h => option_piece_avoids G p (h ▸ p.walk.start_mem_support)
    have htn : p.dst ≠ none := fun h => option_piece_avoids G p (h ▸ p.walk.end_mem_support)
    exact (option_getD_eq v hsn).symm.trans ((congrArg some h).trans (option_getD_eq v htn))

lemma projectOptionPiece_edges (p : Piece (optionBase G)) :
    (projectOptionPiece G v p).walk.edges.map (Sym2.map some) = p.walk.edges := by
  simp only [projectOptionPiece,Walk.edges_map,List.map_map]
  conv_rhs => rw [← List.map_id p.walk.edges]
  apply List.map_congr_left
  intro e he
  have heG := p.walk.edges_subset_edgeSet he
  induction e using Sym2.ind with | h a b =>
    obtain ⟨x,y,hxy,rfl,rfl⟩ := optionBase_adj G |>.mp heG
    rfl

lemma projectOptionPiece_ends (p : Piece (optionBase G)) :
    [some (projectOptionPiece G v p).src,some (projectOptionPiece G v p).dst] =
      [p.src,p.dst] := by
  have hs : p.src ≠ none := fun h => option_piece_avoids G p (h ▸ p.walk.start_mem_support)
  have ht : p.dst ≠ none := fun h => option_piece_avoids G p (h ▸ p.walk.end_mem_support)
  exact congrArg₂ (fun a b => [a,b]) (option_getD_eq v hs) (option_getD_eq v ht)

include v in
lemma project_option_family (L : List (Piece (optionBase G))) :
    ∃ M : List (Piece G), (edgeList M).map (Sym2.map some) = edgeList L ∧
      (endpoints M).map some = endpoints L := by
  induction L with
  | nil => exact ⟨[],rfl,rfl⟩
  | cons p L ih =>
    obtain ⟨M,he,hv⟩ := ih
    refine ⟨projectOptionPiece G v p :: M,?_,?_⟩
    · simp only [edgeList_cons,List.map_append,he,projectOptionPiece_edges]
    · have hp := projectOptionPiece_ends G v p
      have hs := (List.cons.inj hp).1
      have ht := (List.cons.inj (List.cons.inj hp).2).1
      simp only [endpoints_cons,List.map_cons,hv,hs,ht]

end Erdos184Work.OddPaths
#print axioms Erdos184Work.OddPaths.project_option_family
