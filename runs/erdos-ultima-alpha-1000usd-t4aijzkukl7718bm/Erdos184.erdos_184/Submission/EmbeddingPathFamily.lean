import Submission.AttachLeaf

/-! Injective graph maps transport families of simple paths. -/
open SimpleGraph
namespace Erdos184Work.OddPaths
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

def Piece.map (f : G →g H) (hf : Function.Injective f) (p : Piece G) : Piece H :=
  ⟨f p.src,f p.dst,p.walk.map f,p.walk.map_isPath_of_injective hf p.isPath,fun h => p.ne (hf h)⟩

lemma edgeList_map (f : G →g H) (hf : Function.Injective f) (L : List (Piece G)) :
    edgeList (L.map (Piece.map f hf)) = (edgeList L).map (Sym2.map f) := by
  induction L with
  | nil => rfl
  | cons p L ih => simp [Piece.map,Walk.edges_map,ih]

lemma endpoints_map (f : G →g H) (hf : Function.Injective f) (L : List (Piece G)) :
    endpoints (L.map (Piece.map f hf)) = (endpoints L).map f := by
  induction L with
  | nil => rfl
  | cons p L ih => simp [Piece.map,ih]

end Erdos184Work.OddPaths
