import Submission.HeptagonFinite

/-! Expansion of checked seven-cycle / six-visit routes. -/
namespace Erdos583HeptagonRoutesDevelopment
open SimpleGraph Erdos583Work Erdos583Work.PieceRoutes
set_option maxHeartbeats 1800000

lemma cycle_source (p : Fin 6 → Fin 6) (i : Fin 7) :
    pieceSource p (Fin.castAdd 5 i)=i := by simp [pieceSource,i.isLt]

lemma cycle_target (p : Fin 6 → Fin 6) (i : Fin 7) :
    pieceTarget p (Fin.castAdd 5 i)=next i := by simp [pieceTarget,next,i.isLt]

lemma path_source (p : Fin 6 → Fin 6) (i : Fin 5) :
    pieceSource p (Fin.natAdd 7 i)=(p i.castSucc).castSucc := by
  simp [pieceSource,Fin.natAdd,Nat.add_comm]
  rfl

lemma path_target (p : Fin 6 → Fin 6) (i : Fin 5) :
    pieceTarget p (Fin.natAdd 7 i)=(p i.succ).castSucc := by
  simp [pieceTarget,Fin.natAdd,Nat.add_comm]
  rfl

lemma expand_certificate {V : Type*} {G : SimpleGraph V}
    (p : Fin 6 → Fin 6) (hp : Function.Injective p)
    (hfirst : ¬adjacent (p 0) (p 1)) (hlast : ¬adjacent (p 4) (p 5)) (hex : ¬Exceptional p)
    (f : Fin 7 → V) (hf : Function.Injective f)
    (R : ∀ e : Fin 12, G.Walk (f (pieceSource p e)) (f (pieceTarget p e)))
    (hpath : ∀ e, (R e).IsPath)
    (hcore : ∀ e x, f x ∈ (R e).support → x=pieceSource p e ∨ x=pieceTarget p e)
    (hinter : ∀ e j, e ≠ j → ∀ x ∈ (R e).support, x ∈ (R j).support → ∃ a, x=f a)
    (hdis : ∀ e j, e ≠ j → Disjoint (R e).toSubgraph.edgeSet (R j).toSubgraph.edgeSet) :
    ∃ X : G.Walk (f (p 0).castSucc) (f 6), ∃ Y : G.Walk (f (p 5).castSucc) (f 6),
      X.IsPath ∧ Y.IsPath ∧ Disjoint X.toSubgraph.edgeSet Y.toSubgraph.edgeSet ∧
        X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=⋃ e, (R e).toSubgraph.edgeSet := by
  obtain ⟨X,Y,hX,hY,hd,hc⟩ := exists_routes p hp hfirst hlast hex
  exact ⟨X.expand f R,Y.expand f R,Route.expand_two_cover f R hf hpath hcore hinter hdis X Y hX hY hd hc⟩

end Erdos583HeptagonRoutesDevelopment
