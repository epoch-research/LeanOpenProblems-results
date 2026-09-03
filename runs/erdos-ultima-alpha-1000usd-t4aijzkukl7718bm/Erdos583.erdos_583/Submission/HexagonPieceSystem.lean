import Submission.Work
import Submission.HexagonRoutes

/-! Realizing the six-cycle certificates on four consecutive marked path intervals. -/
namespace Erdos583HexagonPieceSystemDevelopment
open SimpleGraph Erdos583Work Erdos583Work.PieceRoutes
open Erdos583HexagonRoutesDevelopment Erdos583Work.PathIntervals Erdos583Work.OrderedPathPieces
set_option maxHeartbeats 2000000
variable {V : Type*} {G : SimpleGraph V} {a b : V}

variable (p : Fin 5 → Fin 5) (f : Fin 6 → V)
variable (P : G.Walk a b) (h : Fin 5 → ℕ) (hh : StrictMono h)
variable (hc : ∀ i, P.getVert (h i)=f (p i).castSucc)
variable (ha : ∀ i : Fin 6, G.Adj (f i) (f (next i)))

def pieces (e : Fin 10) : G.Walk (f (pieceSource p e)) (f (pieceTarget p e)) :=
  Fin.addCases (motive := fun e : Fin 10 ↦ G.Walk (f (pieceSource p e)) (f (pieceTarget p e)))
    (fun i : Fin 6 ↦ (Walk.cons (ha i) Walk.nil).copy
      (congrArg f (cycle_source p i).symm) (congrArg f (cycle_target p i).symm))
    (fun i : Fin 4 ↦ (gap P h hh i).copy
      ((hc i.castSucc).trans (congrArg f (path_source p i).symm))
      ((hc i.succ).trans (congrArg f (path_target p i).symm))) e

lemma cycle_support (i : Fin 6) :
    (pieces p f P h hh hc ha (Fin.castAdd 4 i)).support=[f i,f (next i)] := by
  simp [pieces]

lemma path_support (i : Fin 4) :
    (pieces p f P h hh hc ha (Fin.natAdd 6 i)).support=(gap P h hh i).support := by
  simp [pieces]

lemma cycle_edges (i : Fin 6) :
    (pieces p f P h hh hc ha (Fin.castAdd 4 i)).toSubgraph.edgeSet={s(f i,f (next i))} := by
  ext e
  simp [pieces]

lemma path_edges (i : Fin 4) :
    (pieces p f P h hh hc ha (Fin.natAdd 6 i)).toSubgraph.edgeSet=(gap P h hh i).toSubgraph.edgeSet := by
  ext e
  simp [pieces]

lemma pieces_isPath (hp : P.IsPath) : ∀ e, (pieces p f P h hh hc ha e).IsPath := by
  refine Fin.addCases (m := 6) (n := 4) ?_ ?_
  · intro i
    simp [pieces,(ha i).ne]
  · intro i
    simpa [pieces] using gap_isPath P hp h hh i

lemma pieces_core (hmiss : f 5 ∉ P.support) (hpinj : Function.Injective p) (hf : Function.Injective f) (hp : P.IsPath)
    (hb : ∀ i, h i ≤ P.length) :
    ∀ e x, f x ∈ (pieces p f P h hh hc ha e).support →
      x=pieceSource p e ∨ x=pieceTarget p e := by
  refine Fin.addCases (m := 6) (n := 4) ?_ ?_
  · intro i x hx
    rw [cycle_support] at hx
    rcases (show f x=f i ∨ f x=f (next i) by simpa using hx) with hx|hx
    · exact Or.inl ((hf hx).trans (cycle_source p i).symm)
    · exact Or.inr ((hf hx).trans (cycle_target p i).symm)
  · intro i x hx
    rw [path_support] at hx
    by_cases hxi : x.val < 5
    · let y : Fin 5 := ⟨x.val,hxi⟩
      have hy : y.castSucc=x := Fin.ext rfl
      obtain ⟨j,hj⟩ := (Finite.injective_iff_surjective.mp hpinj) y
      have hx' : P.getVert (h j) ∈ (gap P h hh i).support := by rw [hc j,hj,hy]; exact hx
      rcases (gap_core P hp h hh hb i j).mp hx' with rfl|rfl
      · exact Or.inl (((congrArg Fin.castSucc hj).trans hy).symm.trans (path_source p i).symm)
      · exact Or.inr (((congrArg Fin.castSucc hj).trans hy).symm.trans (path_target p i).symm)
    · have he : x=5 := Fin.ext (by omega)
      have hxP : f x ∈ P.support := by
        obtain ⟨m,_,_,he'⟩ := (interval_support P _ (hb i.succ) (f x)).mp hx
        rw [he']; exact P.getVert_mem_support _
      exact (hmiss (he ▸ hxP)).elim

lemma pieces_intersection (hp : P.IsPath) (hb : ∀ i, h i ≤ P.length) :
    ∀ e j, e ≠ j → ∀ x ∈ (pieces p f P h hh hc ha e).support,
      x ∈ (pieces p f P h hh hc ha j).support → ∃ z, x=f z := by
  refine Fin.addCases (m := 6) (n := 4) ?_ ?_
  · intro i j hij x hx hy
    rw [cycle_support] at hx
    rcases (show x=f i ∨ x=f (next i) by simpa using hx) with hx|hx
    · exact ⟨_,hx⟩
    · exact ⟨_,hx⟩
  · intro i
    refine Fin.addCases (m := 6) (n := 4) ?_ ?_
    · intro j hij x hx hy
      rw [cycle_support] at hy
      rcases (show x=f j ∨ x=f (next j) by simpa using hy) with hy|hy
      · exact ⟨_,hy⟩
      · exact ⟨_,hy⟩
    · intro j hij x hx hy
      rw [path_support] at hx hy
      have hne : i ≠ j := fun he ↦ hij (congrArg (Fin.natAdd 6) he)
      obtain ⟨z,hz⟩ := gap_intersection P hp h hh hb i j hne hx hy
      exact ⟨(p z).castSucc,hz.trans (hc z)⟩

lemma cycle_edge_injective (hf : Function.Injective f) :
    Function.Injective (fun i : Fin 6 ↦ s(f i,f (next i))) := by
  intro i j he
  rcases Sym2.eq_iff.mp he with ⟨he,_⟩|⟨he,he'⟩
  · have hv : i.val=j.val := congrArg (fun x : Fin 6 ↦ x.val) (hf he)
    exact Fin.ext hv
  · have h1 := congrArg Fin.val (hf he)
    have h2 := congrArg Fin.val (hf he')
    dsimp [next] at h1 h2
    omega

lemma pieces_disjoint (hf : Function.Injective f) (hp : P.IsPath) (hb : ∀ i, h i ≤ P.length)
    (havoid : ∀ i : Fin 6, s(f i,f (next i)) ∉ P.edges) :
    ∀ e j, e ≠ j → Disjoint (pieces p f P h hh hc ha e).toSubgraph.edgeSet
      (pieces p f P h hh hc ha j).toSubgraph.edgeSet := by
  refine Fin.addCases (m := 6) (n := 4) ?_ ?_
  · intro i
    refine Fin.addCases (m := 6) (n := 4) ?_ ?_
    · intro j hij
      rw [cycle_edges,cycle_edges]
      apply Set.disjoint_singleton_left.mpr
      intro he
      have he' := cycle_edge_injective f hf he
      exact hij (congrArg (Fin.castAdd 4) he')
    · intro j hij
      rw [cycle_edges,path_edges]
      apply Set.disjoint_singleton_left.mpr
      intro he
      exact havoid i (P.mem_edges_toSubgraph.mp (gap_edges_subset P h hh hb j he))
  · intro i
    refine Fin.addCases (m := 6) (n := 4) ?_ ?_
    · intro j hij
      rw [path_edges,cycle_edges]
      apply Disjoint.symm
      apply Set.disjoint_singleton_left.mpr
      intro he
      exact havoid j (P.mem_edges_toSubgraph.mp (gap_edges_subset P h hh hb i he))
    · intro j hij
      rw [path_edges,path_edges]
      exact gap_edges_disjoint P hp h hh hb i j (fun he ↦ hij (congrArg (Fin.natAdd 6) he))

def cycleEdges : Set (Sym2 V) := ⋃ i : Fin 6, ({s(f i,f (next i))} : Set (Sym2 V))

lemma pieces_cover (hb : ∀ i, h i ≤ P.length) :
    (⋃ e, (pieces p f P h hh hc ha e).toSubgraph.edgeSet)=cycleEdges f ∪
      (interval P (h 0) (h 4) (hh.monotone (Fin.zero_le _))).toSubgraph.edgeSet := by
  rw [show (4 : Fin 5)=Fin.last 4 from rfl,←gap_cover P h hh hb]
  ext e
  simp only [cycleEdges,Set.mem_union,Set.mem_iUnion]
  constructor
  · rintro ⟨j,hj⟩
    have haux : ∀ j : Fin 10, e ∈ (pieces p f P h hh hc ha j).toSubgraph.edgeSet →
        (∃ i : Fin 6, e ∈ ({s(f i,f (next i))} : Set (Sym2 V))) ∨
        ∃ i : Fin 4, e ∈ (gap P h hh i).toSubgraph.edgeSet := by
      refine Fin.addCases (m := 6) (n := 4) ?_ ?_
      · intro i hi
        exact Or.inl ⟨i,(cycle_edges p f P h hh hc ha i) ▸ hi⟩
      · intro i hi
        exact Or.inr ⟨i,(path_edges p f P h hh hc ha i) ▸ hi⟩
    exact haux j hj
  · rintro (⟨i,hi⟩|⟨i,hi⟩)
    · exact ⟨Fin.castAdd 4 i,(cycle_edges p f P h hh hc ha i).symm ▸ hi⟩
    · exact ⟨Fin.natAdd 6 i,(path_edges p f P h hh hc ha i).symm ▸ hi⟩

include hc in
lemma core_in_middle (hpinj : Function.Injective p) (hb : ∀ i, h i ≤ P.length) (x : Fin 5) :
    f x.castSucc ∈ (interval P (h 0) (h 4) (hh.monotone (Fin.zero_le _))).support := by
  obtain ⟨j,hj⟩ := (Finite.injective_iff_surjective.mp hpinj) x
  rw [interval_support P _ (hb 4)]
  exact ⟨h j,hh.monotone (Fin.zero_le _),hh.monotone (Fin.le_last _),by rw [hc j,hj]⟩

lemma pieces_on_path_middle (hmiss : f 5 ∉ P.support)
    (hpinj : Function.Injective p) (hb : ∀ i, h i ≤ P.length) :
    ∀ e x, x ∈ (pieces p f P h hh hc ha e).support → x ∈ P.support →
      x ∈ (interval P (h 0) (h 4) (hh.monotone (Fin.zero_le _))).support := by
  have hcore (i : Fin 6) (hi : f i ∈ P.support) :
      f i ∈ (interval P (h 0) (h 4) (hh.monotone (Fin.zero_le _))).support := by
    have hi5 : i.val < 5 := by
      by_contra hh
      have he : i=5 := Fin.ext (by omega)
      exact hmiss (he ▸ hi)
    exact core_in_middle p f P h hh hc hpinj hb ⟨i.val,hi5⟩
  refine Fin.addCases (m := 6) (n := 4) ?_ ?_
  · intro i x hx hxP
    rw [cycle_support] at hx
    rcases (show x=f i ∨ x=f (next i) by simpa using hx) with rfl|rfl
    · exact hcore i hxP
    · exact hcore (next i) hxP
  · intro i x hx hxP
    rw [path_support,gap,interval_support P _ (hb i.succ)] at hx
    obtain ⟨m,him,hmi,hxm⟩ := hx
    rw [interval_support P _ (hb 4)]
    exact ⟨m,(hh.monotone (Fin.zero_le _)).trans him,hmi.trans (hh.monotone (Fin.le_last _)),hxm⟩

include hc ha in
lemma ordered_absorption (hmiss : f 5 ∉ P.support) (hpinj : Function.Injective p) (hf : Function.Injective f) (hp : P.IsPath)
    (hfirst : ¬adjacent (p 0) (p 1)) (hlast : ¬adjacent (p 3) (p 4))
    (hb : ∀ i, h i ≤ P.length)
    (havoid : ∀ i : Fin 6, s(f i,f (next i)) ∉ P.edges) :
    ∃ X : G.Walk (f (p 0).castSucc) (f 5), ∃ Y : G.Walk (f (p 4).castSucc) (f 5),
      X.IsPath ∧ Y.IsPath ∧ Disjoint X.toSubgraph.edgeSet Y.toSubgraph.edgeSet ∧
        X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=cycleEdges f ∪
          (interval P (h 0) (h 4) (hh.monotone (Fin.zero_le _))).toSubgraph.edgeSet ∧
      (∀ x ∈ X.support, x ∈ P.support → x ∈ (interval P (h 0) (h 4) (hh.monotone (Fin.zero_le _))).support) ∧
      (∀ x ∈ Y.support, x ∈ P.support → x ∈ (interval P (h 0) (h 4) (hh.monotone (Fin.zero_le _))).support) := by
  obtain ⟨X,Y,hX,hY,hd,he⟩ := expand_certificate p hpinj hfirst hlast f hf (pieces p f P h hh hc ha)
    (pieces_isPath p f P h hh hc ha hp) (pieces_core p f P h hh hc ha hmiss hpinj hf hp hb)
    (pieces_intersection p f P h hh hc ha hp hb) (pieces_disjoint p f P h hh hc ha hf hp hb havoid)
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
      (hw : W.toSubgraph.edgeSet ⊆ ⋃ e, (pieces p f P h hh hc ha e).toSubgraph.edgeSet) :
      ∀ x ∈ W.support, x ∈ P.support → x ∈ (interval P (h 0) (h 4) (hh.monotone (Fin.zero_le _))).support := by
    intro x hx hxP
    obtain ⟨y,hy⟩ := VertexTracking.walk_vertex_has_subgraph_neighbor W hn (W.mem_verts_toSubgraph.mpr hx)
    obtain ⟨e,he⟩ := Set.mem_iUnion.mp (hw (show s(x,y) ∈ W.toSubgraph.edgeSet from hy))
    exact pieces_on_path_middle p f P h hh hc ha hmiss hpinj hb e x (Walk.mem_support_of_adj_toSubgraph he) hxP
  exact ⟨X,Y,hX,hY,hd,he.trans (pieces_cover p f P h hh hc ha hb),
    hsupport X hnX (fun e hx ↦ he ▸ Or.inl hx),hsupport Y hnY (fun e hy ↦ he ▸ Or.inr hy)⟩

end Erdos583HexagonPieceSystemDevelopment
