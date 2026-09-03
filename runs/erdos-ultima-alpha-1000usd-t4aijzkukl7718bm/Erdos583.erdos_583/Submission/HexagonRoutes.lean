import Submission.HexagonFinite

/-! Expansion of checked six-cycle / five-visit routes. -/
namespace Erdos583HexagonRoutesDevelopment
open SimpleGraph Erdos583Work Erdos583Work.PieceRoutes
set_option maxHeartbeats 1800000

lemma cycle_source (p : Fin 5 → Fin 5) (i : Fin 6) :
    pieceSource p (Fin.castAdd 4 i)=i := by simp [pieceSource,i.isLt]

lemma cycle_target (p : Fin 5 → Fin 5) (i : Fin 6) :
    pieceTarget p (Fin.castAdd 4 i)=next i := by simp [pieceTarget,next,i.isLt]

lemma path_source (p : Fin 5 → Fin 5) (i : Fin 4) :
    pieceSource p (Fin.natAdd 6 i)=(p i.castSucc).castSucc := by
  simp [pieceSource,Fin.natAdd,Nat.add_comm]
  rfl

lemma path_target (p : Fin 5 → Fin 5) (i : Fin 4) :
    pieceTarget p (Fin.natAdd 6 i)=(p i.succ).castSucc := by
  simp [pieceTarget,Fin.natAdd,Nat.add_comm]
  rfl

lemma expand_certificate {V : Type*} {G : SimpleGraph V}
    (p : Fin 5 → Fin 5) (hp : Function.Injective p)
    (hfirst : ¬adjacent (p 0) (p 1)) (hlast : ¬adjacent (p 3) (p 4))
    (f : Fin 6 → V) (hf : Function.Injective f)
    (R : ∀ e : Fin 10, G.Walk (f (pieceSource p e)) (f (pieceTarget p e)))
    (hpath : ∀ e, (R e).IsPath)
    (hcore : ∀ e x, f x ∈ (R e).support → x=pieceSource p e ∨ x=pieceTarget p e)
    (hinter : ∀ e j, e ≠ j → ∀ x ∈ (R e).support, x ∈ (R j).support → ∃ a, x=f a)
    (hdis : ∀ e j, e ≠ j → Disjoint (R e).toSubgraph.edgeSet (R j).toSubgraph.edgeSet) :
    ∃ X : G.Walk (f (p 0).castSucc) (f 5), ∃ Y : G.Walk (f (p 4).castSucc) (f 5),
      X.IsPath ∧ Y.IsPath ∧ Disjoint X.toSubgraph.edgeSet Y.toSubgraph.edgeSet ∧
        X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=⋃ e, (R e).toSubgraph.edgeSet := by
  obtain ⟨X,Y,hX,hY,hd,hc⟩ := exists_routes p hp hfirst hlast
  exact ⟨X.expand f R,Y.expand f R,Route.expand_two_cover f R hf hpath hcore hinter hdis X Y hX hY hd hc⟩

end Erdos583HexagonRoutesDevelopment
