import Submission.ShortTriangleFourPairChord

/-! Generic expansion of finite core routes together with marked intervals of a path. -/
namespace Erdos583CorePathPiecesDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.TriangleAbsorption
open Erdos583Work.PieceRoutes Erdos583Work.PathIntervals Erdos583Work.OrderedPathPieces
open scoped Classical
set_option maxHeartbeats 2400000
set_option Elab.async false

variable {N M m : ℕ} {V : Type*} {G : SimpleGraph V} {a b : V}

def pieceSource (s : Fin M → Fin N) (q : Fin (m+1) → Fin N) : Fin (M+m) → Fin N :=
  Fin.addCases s (fun i ↦ q i.castSucc)

def pieceTarget (t : Fin M → Fin N) (q : Fin (m+1) → Fin N) : Fin (M+m) → Fin N :=
  Fin.addCases t (fun i ↦ q i.succ)

variable (s t : Fin M → Fin N) (q : Fin (m+1) → Fin N) (f : Fin N → V)
variable (P : G.Walk a b) (h : Fin (m+1) → ℕ) (hh : StrictMono h)
variable (hc : ∀ i, P.getVert (h i)=f (q i))
variable (ha : ∀ i, G.Adj (f (s i)) (f (t i)))

def pieces (e : Fin (M+m)) : G.Walk (f (pieceSource s q e)) (f (pieceTarget t q e)) :=
  Fin.addCases (motive := fun e : Fin (M+m) ↦ G.Walk (f (pieceSource s q e)) (f (pieceTarget t q e)))
    (fun i ↦ (Walk.cons (ha i) Walk.nil).copy (by simp [pieceSource]) (by simp [pieceTarget]))
    (fun i ↦ (gap P h hh i).copy (by simpa [pieceSource] using hc i.castSucc)
      (by simpa [pieceTarget] using hc i.succ)) e

lemma core_support (i : Fin M) :
    (pieces s t q f P h hh hc ha (Fin.castAdd m i)).support=[f (s i),f (t i)] := by
  simp [pieces]

lemma path_support (i : Fin m) :
    (pieces s t q f P h hh hc ha (Fin.natAdd M i)).support=(gap P h hh i).support := by
  simp [pieces]

lemma core_edges (i : Fin M) :
    (pieces s t q f P h hh hc ha (Fin.castAdd m i)).toSubgraph.edgeSet={s(f (s i),f (t i))} := by
  ext e
  simp [pieces]

lemma path_edges (i : Fin m) :
    (pieces s t q f P h hh hc ha (Fin.natAdd M i)).toSubgraph.edgeSet=(gap P h hh i).toSubgraph.edgeSet := by
  ext e
  simp [pieces]

lemma pieces_isPath (hp : P.IsPath) : ∀ e, (pieces s t q f P h hh hc ha e).IsPath := by
  refine Fin.addCases (m := M) (n := m) ?_ ?_
  · intro i; simp [pieces,(ha i).ne]
  · intro i; simpa [pieces] using gap_isPath P hp h hh i

lemma pieces_core (hf : Function.Injective f) (hp : P.IsPath) (hb : ∀ i, h i ≤ P.length)
    (hmarked : ∀ x, f x ∈ P.support → ∃ j, q j=x) :
    ∀ e x, f x ∈ (pieces s t q f P h hh hc ha e).support →
      x=pieceSource s q e ∨ x=pieceTarget t q e := by
  refine Fin.addCases (m := M) (n := m) ?_ ?_
  · intro i x hx
    rw [core_support] at hx
    rcases (show f x=f (s i) ∨ f x=f (t i) by simpa using hx) with hx | hx
    · exact Or.inl (by simpa [pieceSource] using hf hx)
    · exact Or.inr (by simpa [pieceTarget] using hf hx)
  · intro i x hx
    rw [path_support] at hx
    have hxP : f x ∈ P.support := by
      obtain ⟨j,_,_,hj⟩ := (interval_support P _ (hb i.succ) _).mp hx
      rw [hj]; exact P.getVert_mem_support _
    obtain ⟨j,hj⟩ := hmarked x hxP
    have hx' : P.getVert (h j) ∈ (gap P h hh i).support := by rw [hc j,hj]; exact hx
    rcases (gap_core P hp h hh hb i j).mp hx' with hj' | hj'
    · subst j; exact Or.inl (by simpa [pieceSource] using hj.symm)
    · subst j; exact Or.inr (by simpa [pieceTarget] using hj.symm)

lemma pieces_intersection (hp : P.IsPath) (hb : ∀ i, h i ≤ P.length) :
    ∀ e j, e ≠ j → ∀ x ∈ (pieces s t q f P h hh hc ha e).support,
      x ∈ (pieces s t q f P h hh hc ha j).support → ∃ z, x=f z := by
  refine Fin.addCases (m := M) (n := m) ?_ ?_
  · intro i j _ x hx _
    rw [core_support] at hx
    rcases (show x=f (s i) ∨ x=f (t i) by simpa using hx) with hx | hx
    · exact ⟨_,hx⟩
    · exact ⟨_,hx⟩
  · intro i
    refine Fin.addCases (m := M) (n := m) ?_ ?_
    · intro j _ x _ hy
      rw [core_support] at hy
      rcases (show x=f (s j) ∨ x=f (t j) by simpa using hy) with hy | hy
      · exact ⟨_,hy⟩
      · exact ⟨_,hy⟩
    · intro j hij x hx hy
      rw [path_support] at hx hy
      obtain ⟨z,hz⟩ := gap_intersection P hp h hh hb i j
        (fun he ↦ hij (congrArg (Fin.natAdd M) he)) hx hy
      exact ⟨q z,hz.trans (hc z)⟩

lemma pieces_disjoint (hp : P.IsPath) (hb : ∀ i, h i ≤ P.length)
    (heinj : Function.Injective (fun i ↦ s(f (s i),f (t i))))
    (havoid : ∀ i, s(f (s i),f (t i)) ∉ P.edges) :
    ∀ e j, e ≠ j → Disjoint (pieces s t q f P h hh hc ha e).toSubgraph.edgeSet
      (pieces s t q f P h hh hc ha j).toSubgraph.edgeSet := by
  refine Fin.addCases (m := M) (n := m) ?_ ?_
  · intro i
    refine Fin.addCases (m := M) (n := m) ?_ ?_
    · intro j hij
      rw [core_edges,core_edges]
      exact Set.disjoint_singleton_left.mpr (fun he ↦ hij (congrArg (Fin.castAdd m) (heinj he)))
    · intro j _
      rw [core_edges,path_edges]
      exact Set.disjoint_singleton_left.mpr (fun he ↦
        havoid i (P.mem_edges_toSubgraph.mp (gap_edges_subset P h hh hb j he)))
  · intro i
    refine Fin.addCases (m := M) (n := m) ?_ ?_
    · intro j _
      rw [path_edges,core_edges]
      exact (Set.disjoint_singleton_left.mpr (fun he ↦
        havoid j (P.mem_edges_toSubgraph.mp (gap_edges_subset P h hh hb i he)))).symm
    · intro j hij
      rw [path_edges,path_edges]
      exact gap_edges_disjoint P hp h hh hb i j (fun he ↦ hij (congrArg (Fin.natAdd M) he))

def coreEdges : Set (Sym2 V) := ⋃ i, ({s(f (s i),f (t i))} : Set (Sym2 V))

lemma pieces_cover (hb : ∀ i, h i ≤ P.length) :
    (⋃ e, (pieces s t q f P h hh hc ha e).toSubgraph.edgeSet)=coreEdges s t f ∪
      (interval P (h 0) (h (Fin.last m)) (hh.monotone (Fin.zero_le _))).toSubgraph.edgeSet := by
  rw [←gap_cover P h hh hb]
  ext e
  simp only [coreEdges,Set.mem_union,Set.mem_iUnion]
  constructor
  · rintro ⟨j,hj⟩
    have haux : ∀ j : Fin (M+m), e ∈ (pieces s t q f P h hh hc ha j).toSubgraph.edgeSet →
        (∃ i : Fin M, e ∈ ({s(f (s i),f (t i))} : Set (Sym2 V))) ∨
        ∃ i : Fin m, e ∈ (gap P h hh i).toSubgraph.edgeSet := by
      refine Fin.addCases (m := M) (n := m) ?_ ?_
      · intro i hi; exact Or.inl ⟨i,(core_edges s t q f P h hh hc ha i) ▸ hi⟩
      · intro i hi; exact Or.inr ⟨i,(path_edges s t q f P h hh hc ha i) ▸ hi⟩
    exact haux j hj
  · rintro (⟨i,hi⟩|⟨i,hi⟩)
    · exact ⟨Fin.castAdd m i,(core_edges s t q f P h hh hc ha i).symm ▸ hi⟩
    · exact ⟨Fin.natAdd M i,(path_edges s t q f P h hh hc ha i).symm ▸ hi⟩

include hc in
lemma core_in_middle (hb : ∀ i, h i ≤ P.length)
    (hmarked : ∀ x, f x ∈ P.support → ∃ j, q j=x) (x : Fin N) (hx : f x ∈ P.support) :
    f x ∈ (interval P (h 0) (h (Fin.last m)) (hh.monotone (Fin.zero_le _))).support := by
  obtain ⟨j,hj⟩ := hmarked x hx
  rw [interval_support P _ (hb _)]
  exact ⟨h j,hh.monotone (Fin.zero_le _),hh.monotone (Fin.le_last _),
    (congrArg f hj).symm.trans (hc j).symm⟩

lemma pieces_in_middle (hb : ∀ i, h i ≤ P.length)
    (hmarked : ∀ x, f x ∈ P.support → ∃ j, q j=x) :
    ∀ e x, x ∈ (pieces s t q f P h hh hc ha e).support → x ∈ P.support →
      x ∈ (interval P (h 0) (h (Fin.last m)) (hh.monotone (Fin.zero_le _))).support := by
  refine Fin.addCases (m := M) (n := m) ?_ ?_
  · intro i x hx hxP
    rw [core_support] at hx
    rcases (show x=f (s i) ∨ x=f (t i) by simpa using hx) with rfl | rfl
    · exact core_in_middle q f P h hh hc hb hmarked _ hxP
    · exact core_in_middle q f P h hh hc hb hmarked _ hxP
  · intro i x hx _
    rw [path_support,gap,interval_support P _ (hb i.succ)] at hx
    obtain ⟨j,hij,hji,hxj⟩ := hx
    rw [interval_support P _ (hb _)]
    exact ⟨j,(hh.monotone (Fin.zero_le _)).trans hij,hji.trans (hh.monotone (Fin.le_last _)),hxj⟩

include hh hc ha in
lemma absorption_from_routes [Fintype V] (hf : Function.Injective f) (hp : P.IsPath)
    (hb : ∀ i, h i ≤ P.length) (hmarked : ∀ x, f x ∈ P.support → ∃ j, q j=x)
    (heinj : Function.Injective (fun i ↦ s(f (s i),f (t i))))
    (havoid : ∀ i, s(f (s i),f (t i)) ∉ P.edges) {z : Fin N}
    (X : Route (pieceSource s q) (pieceTarget t q) (q 0) z)
    (Y : Route (pieceSource s q) (pieceTarget t q) (q (Fin.last m)) z)
    (hX : X.support.Nodup) (hY : Y.support.Nodup) (hXY : X.pieces.Disjoint Y.pieces)
    (hcov : ∀ e, e ∈ X.pieces ∨ e ∈ Y.pieces) :
    TwoPathCover (G := G) (coreEdges s t f ∪ P.toSubgraph.edgeSet) := by
  let R := pieces s t q f P h hh hc ha
  obtain ⟨hXp,hYp,hd,he⟩ := Route.expand_two_cover f R hf
    (pieces_isPath s t q f P h hh hc ha hp) (pieces_core s t q f P h hh hc ha hf hp hb hmarked)
    (pieces_intersection s t q f P h hh hc ha hp hb)
    (pieces_disjoint s t q f P h hh hc ha hp hb heinj havoid) X Y hX hY hXY hcov
  have hs {u v : Fin N} (W : Route (pieceSource s q) (pieceTarget t q) u v) :
      ∀ x ∈ (W.expand f R).support, x ∈ P.support →
        x ∈ (interval P (h 0) (h (Fin.last m)) (hh.monotone (Fin.zero_le _))).support := by
    intro x hx hxP
    rcases Route.mem_expand_support f R W hx with hx | ⟨e,_,hx⟩
    · rw [hx] at hxP ⊢
      exact core_in_middle q f P h hh hc hb hmarked _ hxP
    · exact pieces_in_middle s t q f P h hh hc ha hb hmarked e x hx hxP
  have hdK : Disjoint (coreEdges s t f) P.toSubgraph.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e he hpE
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
    have hi' : e=s(f (s i),f (t i)) := hi
    subst e
    exact havoid i (P.mem_edges_toSubgraph.mp hpE)
  let X' := (X.expand f R).copy (hc 0).symm rfl
  let Y' := (Y.expand f R).copy (hc (Fin.last m)).symm rfl
  have hXe : X'.toSubgraph=(X.expand f R).toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
  have hYe : Y'.toSubgraph=(Y.expand f R).toSubgraph := NormalTrailSystem.walk_copy_subgraph _ _ _
  apply PathRestoreIntersection.restore_two_on_path P hp (hh.monotone (Fin.zero_le _)) (hb _)
    X' Y' (by simpa only [X',Walk.isPath_copy] using hXp)
    (by simpa only [Y',Walk.isPath_copy] using hYp)
    (by simpa only [hXe,hYe] using hd) (coreEdges s t f) hdK
  · rw [hXe,hYe,he]
    exact pieces_cover s t q f P h hh hc ha hb
  · simpa only [X',Walk.support_copy] using hs X
  · simpa only [Y',Walk.support_copy] using hs Y

end Erdos583CorePathPiecesDevelopment
