import Submission.HeptagonExcursionFinite

/-! Expanding checked heptagon routes. -/
namespace Erdos583HeptagonExcursionRoutesDevelopment
open SimpleGraph Erdos583Work Erdos583Work.PieceRoutes
set_option maxHeartbeats 1800000

lemma extended_zero (p : Fin 7 → Fin 7) (d : Fin 6) : extended p d 0=(p 0).castSucc := by
  simp [extended]

lemma extended_last (p : Fin 7 → Fin 7) (d : Fin 6) : extended p d 7=(p 6).castSucc := by
  have hd := d.isLt
  simp [extended,show ¬7 ≤ d.val by omega,show 7 ≠ d.val+1 by omega]

lemma extended_injective (p : Fin 7 → Fin 7) (hp : Function.Injective p) (d : Fin 6) :
    Function.Injective (extended p d) := by
  intro i j he
  have hh := congrArg Fin.val he
  unfold extended at hh
  split_ifs at hh <;> simp only [Fin.val_castSucc] at hh
  all_goals first
    | exact Fin.ext (by omega)
    | have h := congrArg Fin.val (hp (Fin.ext hh)); exact Fin.ext (by dsimp at h; omega)

lemma cycle_source (p : Fin 7 → Fin 7) (d : Fin 6) (i : Fin 7) :
    pieceSource p d ⟨i.val,by omega⟩=i.castSucc := by simp [pieceSource,i.isLt]

lemma cycle_target (p : Fin 7 → Fin 7) (d : Fin 6) (i : Fin 7) :
    pieceTarget p d ⟨i.val,by omega⟩=(⟨(i.val+1)%7,Nat.mod_lt _ (by decide)⟩ : Fin 7).castSucc := by
  simp [pieceTarget,i.isLt]

lemma path_source (p : Fin 7 → Fin 7) (d : Fin 6) (i : Fin 7) :
    pieceSource p d (Fin.natAdd 7 i)=extended p d i.castSucc := by
  simp [pieceSource,Fin.natAdd,Nat.add_comm]
  rfl

lemma path_target (p : Fin 7 → Fin 7) (d : Fin 6) (i : Fin 7) :
    pieceTarget p d (Fin.natAdd 7 i)=extended p d i.succ := by
  simp [pieceTarget,Fin.natAdd,Nat.add_comm]
  rfl

lemma expand_certificate {V : Type*} {G : SimpleGraph V}
    (p : Fin 7 → Fin 7) (hp : Function.Injective p)
    (hfirst : ¬adjacent (p 0) (p 1)) (hlast : ¬adjacent (p 5) (p 6)) (d : Fin 6) (hg : GoodGap p d)
    (f : Fin 8 → V) (hf : Function.Injective f)
    (R : ∀ e : Fin 14, G.Walk (f (pieceSource p d e)) (f (pieceTarget p d e)))
    (hpath : ∀ e, (R e).IsPath)
    (hcore : ∀ e x, f x ∈ (R e).support → x=pieceSource p d e ∨ x=pieceTarget p d e)
    (hinter : ∀ e j, e ≠ j → ∀ x ∈ (R e).support, x ∈ (R j).support → ∃ a, x=f a)
    (hdis : ∀ e j, e ≠ j → Disjoint (R e).toSubgraph.edgeSet (R j).toSubgraph.edgeSet) :
    ∃ X : G.Walk (f (p 0).castSucc) (f 7), ∃ Y : G.Walk (f (p 6).castSucc) (f 7),
      X.IsPath ∧ Y.IsPath ∧ Disjoint X.toSubgraph.edgeSet Y.toSubgraph.edgeSet ∧
        X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=⋃ e, (R e).toSubgraph.edgeSet := by
  obtain ⟨X,Y,hX,hY,hd,hc⟩ := exists_routes p hp hfirst hlast d hg
  exact ⟨X.expand f R,Y.expand f R,Route.expand_two_cover f R hf hpath hcore hinter hdis X Y hX hY hd hc⟩

end Erdos583HeptagonExcursionRoutesDevelopment
