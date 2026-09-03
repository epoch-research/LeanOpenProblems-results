import Submission.Work
import Submission.PieceRoutes
import Submission.PentagonRoutes
import Submission.PathIntervals
import Submission.OrderedPathPieces

/-! Realizing the finite pentagon certificates on consecutive subpaths. -/
namespace Erdos583PentagonPieceSystemDevelopment
open SimpleGraph Erdos583Work Erdos583PieceRoutesDevelopment
open Erdos583PentagonRoutesDevelopment Erdos583PathIntervalsDevelopment Erdos583OrderedPathPiecesDevelopment
set_option maxHeartbeats 2000000
variable {V : Type*} {G : SimpleGraph V} {a b : V}

def next (i : Fin 5) : Fin 5 := ⟨(i.val+1)%5,Nat.mod_lt _ (by decide)⟩

variable (p : Fin 5 → Fin 5) (d : Fin 4) (f : Fin 6 → V)
variable (P : G.Walk a b) (h : Fin 6 → ℕ) (hh : StrictMono h)
variable (hc : ∀ i, P.getVert (h i)=f (extended p d i))
variable (ha : ∀ i : Fin 5, G.Adj (f i.castSucc) (f (next i).castSucc))

def pieces (e : Fin 10) : G.Walk (f (pieceSource p d e)) (f (pieceTarget p d e)) :=
  Fin.addCases (motive := fun e : Fin 10 ↦ G.Walk (f (pieceSource p d e)) (f (pieceTarget p d e)))
    (fun i : Fin 5 ↦ (Walk.cons (ha i) Walk.nil).copy
      (congrArg f (cycle_source p d i).symm) (congrArg f (cycle_target p d i).symm))
    (fun i : Fin 5 ↦ (gap P h hh i).copy
      ((hc i.castSucc).trans (congrArg f (path_source p d i).symm))
      ((hc i.succ).trans (congrArg f (path_target p d i).symm))) e

lemma cycle_support (i : Fin 5) :
    (pieces p d f P h hh hc ha (Fin.castAdd 5 i)).support=[f i.castSucc,f (next i).castSucc] := by
  simp [pieces]

lemma path_support (i : Fin 5) :
    (pieces p d f P h hh hc ha (Fin.natAdd 5 i)).support=(gap P h hh i).support := by
  simp [pieces]

lemma cycle_edges (i : Fin 5) :
    (pieces p d f P h hh hc ha (Fin.castAdd 5 i)).toSubgraph.edgeSet={s(f i.castSucc,f (next i).castSucc)} := by
  ext e
  simp [pieces]

lemma path_edges (i : Fin 5) :
    (pieces p d f P h hh hc ha (Fin.natAdd 5 i)).toSubgraph.edgeSet=(gap P h hh i).toSubgraph.edgeSet := by
  ext e
  simp [pieces]

lemma pieces_isPath (hp : P.IsPath) : ∀ e, (pieces p d f P h hh hc ha e).IsPath := by
  refine Fin.addCases (m := 5) (n := 5) ?_ ?_
  · intro i
    simp [pieces,(ha i).ne]
  · intro i
    simpa [pieces] using gap_isPath P hp h hh i

lemma pieces_core (hpinj : Function.Injective p) (hf : Function.Injective f) (hp : P.IsPath)
    (hb : ∀ i, h i ≤ P.length) :
    ∀ e x, f x ∈ (pieces p d f P h hh hc ha e).support →
      x=pieceSource p d e ∨ x=pieceTarget p d e := by
  refine Fin.addCases (m := 5) (n := 5) ?_ ?_
  · intro i x hx
    rw [cycle_support] at hx
    rcases (show f x=f i.castSucc ∨ f x=f (next i).castSucc by simpa using hx) with hx|hx
    · exact Or.inl ((hf hx).trans (cycle_source p d i).symm)
    · exact Or.inr ((hf hx).trans (cycle_target p d i).symm)
  · intro i x hx
    have hq := (Finite.injective_iff_surjective.mp (extended_injective p hpinj d))
    obtain ⟨j,hj⟩ := hq x
    rw [path_support] at hx
    have hx' : P.getVert (h j) ∈ (gap P h hh i).support := by rw [hc j,hj]; exact hx
    rcases (gap_core P hp h hh hb i j).mp hx' with rfl|rfl
    · exact Or.inl (hj.symm.trans (path_source p d i).symm)
    · exact Or.inr (hj.symm.trans (path_target p d i).symm)

lemma pieces_intersection (hp : P.IsPath) (hb : ∀ i, h i ≤ P.length) :
    ∀ e j, e ≠ j → ∀ x ∈ (pieces p d f P h hh hc ha e).support,
      x ∈ (pieces p d f P h hh hc ha j).support → ∃ z, x=f z := by
  refine Fin.addCases (m := 5) (n := 5) ?_ ?_
  · intro i j hij x hx hy
    rw [cycle_support] at hx
    rcases (show x=f i.castSucc ∨ x=f (next i).castSucc by simpa using hx) with hx|hx
    · exact ⟨_,hx⟩
    · exact ⟨_,hx⟩
  · intro i
    refine Fin.addCases (m := 5) (n := 5) ?_ ?_
    · intro j hij x hx hy
      rw [cycle_support] at hy
      rcases (show x=f j.castSucc ∨ x=f (next j).castSucc by simpa using hy) with hy|hy
      · exact ⟨_,hy⟩
      · exact ⟨_,hy⟩
    · intro j hij x hx hy
      rw [path_support] at hx hy
      have hne : i ≠ j := fun he ↦ hij (congrArg (Fin.natAdd 5) he)
      obtain ⟨z,hz⟩ := gap_intersection P hp h hh hb i j hne hx hy
      exact ⟨extended p d z,hz.trans (hc z)⟩

lemma cycle_edge_injective (hf : Function.Injective f) :
    Function.Injective (fun i : Fin 5 ↦ s(f i.castSucc,f (next i).castSucc)) := by
  intro i j he
  rcases Sym2.eq_iff.mp he with ⟨he,_⟩|⟨he,he'⟩
  · have hv : i.val=j.val := congrArg (fun x : Fin 6 ↦ x.val) (hf he)
    exact Fin.ext hv
  · have h1 := congrArg Fin.val (hf he)
    have h2 := congrArg Fin.val (hf he')
    dsimp [next] at h1 h2
    omega

lemma pieces_disjoint (hf : Function.Injective f) (hp : P.IsPath) (hb : ∀ i, h i ≤ P.length)
    (havoid : ∀ i : Fin 5, s(f i.castSucc,f (next i).castSucc) ∉ P.edges) :
    ∀ e j, e ≠ j → Disjoint (pieces p d f P h hh hc ha e).toSubgraph.edgeSet
      (pieces p d f P h hh hc ha j).toSubgraph.edgeSet := by
  refine Fin.addCases (m := 5) (n := 5) ?_ ?_
  · intro i
    refine Fin.addCases (m := 5) (n := 5) ?_ ?_
    · intro j hij
      rw [cycle_edges,cycle_edges]
      apply Set.disjoint_singleton_left.mpr
      intro he
      have he' := cycle_edge_injective f hf he
      exact hij (congrArg (Fin.castAdd 5) he')
    · intro j hij
      rw [cycle_edges,path_edges]
      apply Set.disjoint_singleton_left.mpr
      intro he
      exact havoid i (P.mem_edges_toSubgraph.mp (gap_edges_subset P h hh hb j he))
  · intro i
    refine Fin.addCases (m := 5) (n := 5) ?_ ?_
    · intro j hij
      rw [path_edges,cycle_edges]
      apply Disjoint.symm
      apply Set.disjoint_singleton_left.mpr
      intro he
      exact havoid j (P.mem_edges_toSubgraph.mp (gap_edges_subset P h hh hb i he))
    · intro j hij
      rw [path_edges,path_edges]
      exact gap_edges_disjoint P hp h hh hb i j (fun he ↦ hij (congrArg (Fin.natAdd 5) he))

def cycleEdges : Set (Sym2 V) := ⋃ i : Fin 5, ({s(f i.castSucc,f (next i).castSucc)} : Set (Sym2 V))

lemma pieces_cover (hb : ∀ i, h i ≤ P.length) :
    (⋃ e, (pieces p d f P h hh hc ha e).toSubgraph.edgeSet)=cycleEdges f ∪
      (interval P (h 0) (h 5) (hh.monotone (Fin.zero_le _))).toSubgraph.edgeSet := by
  rw [show (5 : Fin 6)=Fin.last 5 from rfl,←gap_cover P h hh hb]
  ext e
  simp only [cycleEdges,Set.mem_union,Set.mem_iUnion]
  constructor
  · rintro ⟨j,hj⟩
    have haux : ∀ j : Fin 10, e ∈ (pieces p d f P h hh hc ha j).toSubgraph.edgeSet →
        (∃ i : Fin 5, e ∈ ({s(f i.castSucc,f (next i).castSucc)} : Set (Sym2 V))) ∨
        ∃ i : Fin 5, e ∈ (gap P h hh i).toSubgraph.edgeSet := by
      refine Fin.addCases (m := 5) (n := 5) ?_ ?_
      · intro i hi
        exact Or.inl ⟨i,(cycle_edges p d f P h hh hc ha i) ▸ hi⟩
      · intro i hi
        exact Or.inr ⟨i,(path_edges p d f P h hh hc ha i) ▸ hi⟩
    exact haux j hj
  · rintro (⟨i,hi⟩|⟨i,hi⟩)
    · exact ⟨Fin.castAdd 5 i,(cycle_edges p d f P h hh hc ha i).symm ▸ hi⟩
    · exact ⟨Fin.natAdd 5 i,(path_edges p d f P h hh hc ha i).symm ▸ hi⟩

include hc in
lemma core_in_middle (hpinj : Function.Injective p) (hb : ∀ i, h i ≤ P.length) (x : Fin 6) :
    f x ∈ (interval P (h 0) (h 5) (hh.monotone (Fin.zero_le _))).support := by
  obtain ⟨j,hj⟩ := (Finite.injective_iff_surjective.mp (extended_injective p hpinj d)) x
  rw [interval_support P _ (hb 5)]
  exact ⟨h j,hh.monotone (Fin.zero_le _),hh.monotone (Fin.le_last _),(congrArg f hj).symm.trans (hc j).symm⟩

lemma pieces_in_middle (hpinj : Function.Injective p) (hb : ∀ i, h i ≤ P.length) :
    ∀ e x, x ∈ (pieces p d f P h hh hc ha e).support →
      x ∈ (interval P (h 0) (h 5) (hh.monotone (Fin.zero_le _))).support := by
  refine Fin.addCases (m := 5) (n := 5) ?_ ?_
  · intro i x hx
    rw [cycle_support] at hx
    rcases (show x=f i.castSucc ∨ x=f (next i).castSucc by simpa using hx) with rfl|rfl
    · exact core_in_middle p d f P h hh hc hpinj hb _
    · exact core_in_middle p d f P h hh hc hpinj hb _
  · intro i x hx
    rw [path_support, gap,interval_support P _ (hb i.succ)] at hx
    obtain ⟨m,him,hmi,hxm⟩ := hx
    rw [interval_support P _ (hb 5)]
    exact ⟨m,(hh.monotone (Fin.zero_le _)).trans him,hmi.trans (hh.monotone (Fin.le_last _)),hxm⟩

include hc ha in
lemma ordered_absorption (hpinj : Function.Injective p) (hf : Function.Injective f) (hp : P.IsPath)
    (hfirst : ¬adjacent (p 0) (p 1)) (hlast : ¬adjacent (p 3) (p 4))
    (hb : ∀ i, h i ≤ P.length)
    (havoid : ∀ i : Fin 5, s(f i.castSucc,f (next i).castSucc) ∉ P.edges) :
    ∃ X : G.Walk (f (p 0).castSucc) (f 5), ∃ Y : G.Walk (f (p 4).castSucc) (f 5),
      X.IsPath ∧ Y.IsPath ∧ Disjoint X.toSubgraph.edgeSet Y.toSubgraph.edgeSet ∧
        X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=cycleEdges f ∪
          (interval P (h 0) (h 5) (hh.monotone (Fin.zero_le _))).toSubgraph.edgeSet ∧
      (∀ x ∈ X.support, x ∈ (interval P (h 0) (h 5) (hh.monotone (Fin.zero_le _))).support) ∧
      (∀ x ∈ Y.support, x ∈ (interval P (h 0) (h 5) (hh.monotone (Fin.zero_le _))).support) := by
  obtain ⟨X,Y,hX,hY,hd,he⟩ := expand_certificate p hpinj hfirst hlast d f hf (pieces p d f P h hh hc ha)
    (pieces_isPath p d f P h hh hc ha hp) (pieces_core p d f P h hh hc ha hpinj hf hp hb)
    (pieces_intersection p d f P h hh hc ha hp hb) (pieces_disjoint p d f P h hh hc ha hf hp hb havoid)
  have hnX : ¬X.Nil := Walk.not_nil_of_ne (by
    intro hh
    have hv := congrArg (fun z : Fin 6 ↦ z.val) (hf hh)
    have hp0 := (p 0).isLt
    simp only [Fin.val_castSucc] at hv
    omega)
  have hnY : ¬Y.Nil := Walk.not_nil_of_ne (by
    intro hh
    have hv := congrArg (fun z : Fin 6 ↦ z.val) (hf hh)
    have hp4 := (p 4).isLt
    simp only [Fin.val_castSucc] at hv
    omega)
  have hsupport {u v : V} (W : G.Walk u v) (hn : ¬W.Nil)
      (hw : W.toSubgraph.edgeSet ⊆ ⋃ e, (pieces p d f P h hh hc ha e).toSubgraph.edgeSet) :
      ∀ x ∈ W.support, x ∈ (interval P (h 0) (h 5) (hh.monotone (Fin.zero_le _))).support := by
    intro x hx
    obtain ⟨y,hy⟩ := VertexTracking.walk_vertex_has_subgraph_neighbor W hn (W.mem_verts_toSubgraph.mpr hx)
    obtain ⟨e,he⟩ := Set.mem_iUnion.mp (hw (show s(x,y) ∈ W.toSubgraph.edgeSet from hy))
    exact pieces_in_middle p d f P h hh hc ha hpinj hb e x (Walk.mem_support_of_adj_toSubgraph he)
  exact ⟨X,Y,hX,hY,hd,he.trans (pieces_cover p d f P h hh hc ha hb),
    hsupport X hnX (fun e hx ↦ he ▸ Or.inl hx),hsupport Y hnY (fun e hy ↦ he ▸ Or.inr hy)⟩

end Erdos583PentagonPieceSystemDevelopment
