import Submission.Work

/-! Local absorption of a quadrilateral into an intersecting path.
This is a local exchange, not an assertion of the general Gallai bound. -/
namespace Erdos583QuadrilateralAbsorptionDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583Work.TriangleAbsorption
open scoped Classical
set_option maxHeartbeats 1600000

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
lemma mem_concat_support {a b c : V} (P : G.Walk a b) (h : G.Adj b c) (x : V) :
    x ∈ (P.concat h).support ↔ x=c ∨ x ∈ P.support := by
  simp only [Walk.support_concat,List.concat_eq_append,List.mem_append,List.mem_singleton]
  tauto

abbrev squareEdges (u v w z : V) : Set (Sym2 V) :=
  {s(u,v),s(v,w),s(w,z),s(z,u)}

omit [Fintype V] in
lemma square_edges_ncard {u v w z : V}
    (huv : u ≠ v) (hvw : v ≠ w) (hwz : w ≠ z) (hzu : z ≠ u)
    (huw : u ≠ w) (hvz : v ≠ z) : (squareEdges u v w z).ncard=4 := by
  have h1 : s(u,v) ≠ s(v,w) := fun h ↦
    (Sym2.eq_iff.mp h).elim (fun h ↦ huv h.1) (fun h ↦ huw h.1)
  have h2 : s(u,v) ≠ s(w,z) := fun h ↦
    (Sym2.eq_iff.mp h).elim (fun h ↦ huw h.1) (fun h ↦ hzu h.1.symm)
  have h3 : s(u,v) ≠ s(z,u) := fun h ↦
    (Sym2.eq_iff.mp h).elim (fun h ↦ hzu h.1.symm) (fun h ↦ hvz h.2)
  have h4 : s(v,w) ≠ s(w,z) := fun h ↦
    (Sym2.eq_iff.mp h).elim (fun h ↦ hvw h.1) (fun h ↦ hvz h.1)
  have h5 : s(v,w) ≠ s(z,u) := fun h ↦
    (Sym2.eq_iff.mp h).elim (fun h ↦ hvz h.1) (fun h ↦ huv h.1.symm)
  have h6 : s(w,z) ≠ s(z,u) := fun h ↦
    (Sym2.eq_iff.mp h).elim (fun h ↦ hwz h.1) (fun h ↦ huw h.1.symm)
  simp [squareEdges,Set.ncard_insert_of_notMem,h1,h2,h3,h4,h5,h6]

lemma square_union_ncard {a b u v w z : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwz : G.Adj w z) (hzu : G.Adj z u)
    (huw : u ≠ w) (hvz : v ≠ z) (P : G.Walk a b) (hp : P.IsPath)
    (hd : Disjoint P.toSubgraph.edgeSet (squareEdges u v w z)) :
    (P.toSubgraph.edgeSet ∪ squareEdges u v w z).ncard=P.length+4 := by
  rw [Set.ncard_union_eq hd,trail_edgeSet_ncard P hp.isTrail,
    square_edges_ncard huv.ne hvw.ne hwz.ne hzu.ne huw hvz]

/-- The first cycle vertex has a missing neighbor on the quadrilateral. -/
lemma missing_corner {a b u v w z : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwz : G.Adj w z) (hzu : G.Adj z u)
    (huw : u ≠ w) (hvz : v ≠ z)
    (A : G.Walk a u) (D : G.Walk u b) (hp : (A.append D).IsPath)
    (hvA : v ∉ A.support) (hwA : w ∉ A.support) (hzA : z ∉ A.support)
    (hvD : v ∉ D.support)
    (hd : Disjoint (A.append D).toSubgraph.edgeSet (squareEdges u v w z)) :
    TwoPathCover (G := G) ((A.append D).toSubgraph.edgeSet ∪ squareEdges u v w z) := by
  let X := ((A.concat hzu.symm).concat hwz.symm).concat hvw.symm
  let Y := Walk.cons huv.symm D
  have hX : X.IsPath := by
    apply Walk.IsPath.concat
    · apply Walk.IsPath.concat
      · exact hp.of_append_left.concat hzA hzu.symm
      · simpa only [mem_concat_support,not_or] using ⟨hwz.ne,hwA⟩
    · simp only [mem_concat_support,not_or]
      exact ⟨hvw.ne,hvz,hvA⟩
  have hY : Y.IsPath := (Walk.cons_isPath_iff huv.symm D).mpr ⟨hp.of_append_right,hvD⟩
  have he : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet =
      (A.append D).toSubgraph.edgeSet ∪ squareEdges u v w z := by
    ext e
    simp only [X,Y,squareEdges,Set.mem_union,Walk.mem_edges_toSubgraph,Walk.edges_concat,
      Walk.edges_cons,Walk.edges_append,List.concat_eq_append,List.mem_append,
      List.mem_cons,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := u) (b := z),
      Sym2.eq_swap (a := z) (b := w),Sym2.eq_swap (a := w) (b := v),Sym2.eq_swap (a := v) (b := u)]
    tauto
  have hn : X.length+Y.length=((A.append D).toSubgraph.edgeSet ∪ squareEdges u v w z).ncard := by
    rw [square_union_ncard huv hvw hwz hzu huw hvz _ hp hd]
    simp only [X,Y,Walk.length_concat,Walk.length_cons,Walk.length_append]
    omega
  exact ⟨a,v,v,b,X,Y,hX,hY,disjoint_of_cover_length X Y hX.isTrail hY.isTrail _ he hn,he⟩

/-- The first two cycle vertices visited by the old path are adjacent.
The first old-path edge between them is not the quadrilateral edge. -/
lemma adjacent_first {a b u v w z x : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwz : G.Adj w z) (hzu : G.Adj z u)
    (huw : u ≠ w) (hvz : v ≠ z)
    (A : G.Walk a u) (h : G.Adj u x) (R : G.Walk x v) (D : G.Walk v b)
    (hp : (A.append (Walk.cons h (R.append D))).IsPath)
    (hvA : v ∉ A.support) (hwA : w ∉ A.support) (hzA : z ∉ A.support)
    (hwR : w ∉ R.support) (hzR : z ∉ R.support)
    (hd : Disjoint (A.append (Walk.cons h (R.append D))).toSubgraph.edgeSet
      (squareEdges u v w z)) :
    TwoPathCover (G := G) ((A.append (Walk.cons h (R.append D))).toSubgraph.edgeSet ∪
      squareEdges u v w z) := by
  let P := A.append (Walk.cons h (R.append D))
  have hRD := hp.of_append_right.of_cons
  have hcross := append_cons_support_disjoint A h (R.append D) hp
  have hAR (t : V) (ht : t ∈ A.support) (hr : t ∈ R.support) : False :=
    hcross t ht ((R.mem_support_append_iff D).mpr (Or.inl hr))
  have hAD (t : V) (ht : t ∈ A.support) (hr : t ∈ D.support) : False :=
    hcross t ht ((R.mem_support_append_iff D).mpr (Or.inr hr))
  have hxv : x ≠ v := by
    intro hh
    apply Set.disjoint_left.mp hd (show s(u,x) ∈ P.toSubgraph.edgeSet by simp [P])
    simp [squareEdges,hh]
  have hxD : x ∉ D.support := fun hh ↦
    (hRD.ne_of_mem_support_of_append hxv R.start_mem_support hh) rfl
  have huD : u ∉ D.support := hAD u A.end_mem_support
  let L := ((A.concat hzu.symm).concat hwz.symm).concat hvw.symm
  let X := L.append R.reverse
  let Y := Walk.cons h.symm (Walk.cons huv D)
  have hL : L.IsPath := by
    apply Walk.IsPath.concat
    · apply Walk.IsPath.concat
      · exact hp.of_append_left.concat hzA hzu.symm
      · simpa only [mem_concat_support,not_or] using ⟨hwz.ne,hwA⟩
    · simp only [mem_concat_support,not_or]
      exact ⟨hvw.ne,hvz,hvA⟩
  have hX : X.IsPath := by
    apply path_append_of_support_intersection hL hRD.of_append_left.reverse
    intro t ht hR
    have htR : t ∈ R.support := by simpa using hR
    simp only [L,mem_concat_support] at ht
    rcases ht with rfl|rfl|rfl|ht
    · rfl
    · exact (hwR htR).elim
    · exact (hzR htR).elim
    · exact (hAR t ht htR).elim
  have hY : Y.IsPath := by
    simp only [Y,Walk.cons_isPath_iff,Walk.support_cons,List.mem_cons,not_or]
    exact ⟨⟨hRD.of_append_right,huD⟩,h.ne.symm,hxD⟩
  have he : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet =
      P.toSubgraph.edgeSet ∪ squareEdges u v w z := by
    ext e
    simp only [X,Y,L,P,squareEdges,Set.mem_union,Walk.mem_edges_toSubgraph,Walk.edges_concat,
      Walk.edges_cons,Walk.edges_append,Walk.edges_reverse,List.concat_eq_append,List.mem_append,
      List.mem_cons,List.mem_reverse,Set.mem_insert_iff,Set.mem_singleton_iff,
      Sym2.eq_swap (a := u) (b := z),Sym2.eq_swap (a := z) (b := w),
      Sym2.eq_swap (a := w) (b := v),Sym2.eq_swap (a := x) (b := u)]
    tauto
  have hn : X.length+Y.length=(P.toSubgraph.edgeSet ∪ squareEdges u v w z).ncard := by
    rw [square_union_ncard huv hvw hwz hzu huw hvz _ hp hd]
    simp only [X,Y,L,Walk.length_concat,Walk.length_cons,Walk.length_append,Walk.length_reverse]
    omega
  exact ⟨a,x,x,b,X,Y,hX,hY,disjoint_of_cover_length X Y hX.isTrail hY.isTrail _ he hn,he⟩

/-- The crossing order u,w,v,z. The old path has a non-cycle edge w-x
between its middle two quadrilateral visits. -/
lemma crossing_order {a b u v w z x : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwz : G.Adj w z) (hzu : G.Adj z u)
    (huw : u ≠ w) (hvz : v ≠ z)
    (A : G.Walk a u) (B : G.Walk u w) (h : G.Adj w x)
    (R : G.Walk x v) (D : G.Walk v z) (E : G.Walk z b)
    (hp : ((A.append B).append (Walk.cons h (R.append (D.append E)))).IsPath)
    (hd : Disjoint ((A.append B).append (Walk.cons h (R.append (D.append E)))).toSubgraph.edgeSet
      (squareEdges u v w z)) :
    TwoPathCover (G := G)
      (((A.append B).append (Walk.cons h (R.append (D.append E)))).toSubgraph.edgeSet ∪
        squareEdges u v w z) := by
  let P := (A.append B).append (Walk.cons h (R.append (D.append E)))
  have hAB := hp.of_append_left
  have hRDE := hp.of_append_right.of_cons
  have hDE := hRDE.of_append_right
  have hcross := append_cons_support_disjoint (A.append B) h (R.append (D.append E)) hp
  have hAR (t : V) (ha : t ∈ A.support) (hr : t ∈ R.support) : False :=
    hcross t (by simp only [Walk.mem_support_append_iff]; exact Or.inl ha)
      (by simp only [Walk.mem_support_append_iff]; exact Or.inl hr)
  have hAD (t : V) (ha : t ∈ A.support) (hr : t ∈ D.support) : False :=
    hcross t (by simp only [Walk.mem_support_append_iff]; exact Or.inl ha)
      (by simp only [Walk.mem_support_append_iff]; exact Or.inr (Or.inl hr))
  have hBR (t : V) (ha : t ∈ B.support) (hr : t ∈ R.support) : False :=
    hcross t (by simp only [Walk.mem_support_append_iff]; exact Or.inr ha)
      (by simp only [Walk.mem_support_append_iff]; exact Or.inl hr)
  have hBD (t : V) (ha : t ∈ B.support) (hr : t ∈ D.support) : False :=
    hcross t (by simp only [Walk.mem_support_append_iff]; exact Or.inr ha)
      (by simp only [Walk.mem_support_append_iff]; exact Or.inr (Or.inl hr))
  have hBE (t : V) (ha : t ∈ B.support) (hr : t ∈ E.support) : False :=
    hcross t (by simp only [Walk.mem_support_append_iff]; exact Or.inr ha)
      (by simp only [Walk.mem_support_append_iff]; exact Or.inr (Or.inr hr))
  have hwA : w ∉ A.support := fun hh ↦
    (hAB.ne_of_mem_support_of_append huw.symm hh B.end_mem_support) rfl
  have hvA : v ∉ A.support := fun hh ↦ hAR v hh R.end_mem_support
  have hxA : x ∉ A.support := fun hh ↦ hAR x hh R.start_mem_support
  have hwR : w ∉ R.support := hBR w B.end_mem_support
  have hwD : w ∉ D.support := hBD w B.end_mem_support
  have hwE : w ∉ E.support := hBE w B.end_mem_support
  have hzB : z ∉ B.support := fun hh ↦ hBD z hh D.end_mem_support
  have hxv : x ≠ v := by
    intro hh
    apply Set.disjoint_left.mp hd (show s(w,x) ∈ P.toSubgraph.edgeSet by simp [P])
    simp [squareEdges,hh,Sym2.eq_swap (a := w) (b := v)]
  have hxD : x ∉ D.support := fun hh ↦
    (hRDE.ne_of_mem_support_of_append hxv R.start_mem_support
      ((D.mem_support_append_iff E).mpr (Or.inl hh))) rfl
  have hzR : z ∉ R.support := fun hh ↦
    (hRDE.ne_of_mem_support_of_append hvz.symm hh
      ((D.mem_support_append_iff E).mpr (Or.inl D.end_mem_support))) rfl
  have hRE (t : V) (hr : t ∈ R.support) (he : t ∈ E.support) : False := by
    by_cases ht : t=v
    · subst t
      exact (hDE.ne_of_mem_support_of_append hvz D.start_mem_support he) rfl
    · exact (hRDE.ne_of_mem_support_of_append ht hr
        ((D.mem_support_append_iff E).mpr (Or.inr he))) rfl
  let X₀ := (A.concat huv).append D
  let X := (X₀.concat hwz.symm).concat h
  let Y₀ := (R.concat hvw).append B.reverse
  let Y := (Y₀.concat hzu.symm).append E
  have hX₀ : X₀.IsPath := by
    apply path_append_of_support_intersection (hAB.of_append_left.concat hvA huv) hDE.of_append_left
    intro t ht htD
    rcases (mem_concat_support A huv t).mp ht with rfl|ht
    · rfl
    · exact (hAD t ht htD).elim
  have hX : X.IsPath := by
    apply Walk.IsPath.concat
    · apply hX₀.concat
      simp only [X₀,Walk.mem_support_append_iff,mem_concat_support,not_or]
      exact ⟨⟨hvw.ne.symm,hwA⟩,hwD⟩
    · simp only [X₀,Walk.mem_support_append_iff,mem_concat_support,not_or]
      exact ⟨h.ne.symm,⟨hxv,hxA⟩,hxD⟩
  have hY₀ : Y₀.IsPath := by
    apply path_append_of_support_intersection (hRDE.of_append_left.concat hwR hvw) hAB.of_append_right.reverse
    intro t ht htB
    have htB' : t ∈ B.support := by simpa using htB
    rcases (mem_concat_support R hvw t).mp ht with rfl|ht
    · rfl
    · exact (hBR t htB' ht).elim
  have hzY₀ : z ∉ Y₀.support := by
    simp only [Y₀,Walk.mem_support_append_iff,mem_concat_support,Walk.support_reverse,List.mem_reverse,not_or]
    exact ⟨⟨hwz.ne.symm,hzR⟩,hzB⟩
  have hY : Y.IsPath := by
    apply path_append_of_support_intersection (hY₀.concat hzY₀ hzu.symm) hDE.of_append_right
    intro t ht htE
    simp only [Y₀,mem_concat_support,Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse] at ht
    rcases ht with rfl|((rfl|ht)|ht)
    · rfl
    · exact (hwE htE).elim
    · exact (hRE t ht htE).elim
    · exact (hBE t ht htE).elim
  have he : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet =
      P.toSubgraph.edgeSet ∪ squareEdges u v w z := by
    ext e
    simp only [X,Y,X₀,Y₀,P,squareEdges,Set.mem_union,Walk.mem_edges_toSubgraph,Walk.edges_concat,
      Walk.edges_cons,Walk.edges_append,Walk.edges_reverse,List.concat_eq_append,List.mem_append,
      List.mem_cons,List.mem_reverse,Set.mem_insert_iff,Set.mem_singleton_iff,
      Sym2.eq_swap (a := z) (b := w),Sym2.eq_swap (a := u) (b := z)]
    tauto
  have hn : X.length+Y.length=(P.toSubgraph.edgeSet ∪ squareEdges u v w z).ncard := by
    rw [square_union_ncard huv hvw hwz hzu huw hvz _ hp hd]
    simp only [X,Y,X₀,Y₀,Walk.length_concat,Walk.length_cons,Walk.length_append,Walk.length_reverse]
    omega
  exact ⟨a,x,x,b,X,Y,hX,hY,disjoint_of_cover_length X Y hX.isTrail hY.isTrail _ he hn,he⟩

omit [Fintype V] in
lemma first_hit_split {a b : V} (P : G.Walk a b) (S : Set V)
    (hhit : ∃ x ∈ P.support, x ∈ S) :
    ∃ u ∈ S, ∃ A : G.Walk a u, ∃ D : G.Walk u b,
      P=A.append D ∧ ∀ x ∈ A.support, x ∈ S → x=u := by
  obtain ⟨u,hu,A,D,hP,hA⟩ := CycleDefect.last_hit_split P.reverse S (by simpa using hhit)
  refine ⟨u,hu,D.reverse,A.reverse,?_,?_⟩
  · have hh := congrArg Walk.reverse hP
    simpa only [Walk.reverse_reverse,Walk.reverse_append] using hh
  · intro x hx hs
    exact hA x (by simpa using hx) hs

omit [Fintype V] in
lemma square_edges_reverse (u v w z : V) :
    squareEdges u z w v = squareEdges u v w z := by
  ext e
  simp only [squareEdges,Set.mem_insert_iff,Set.mem_singleton_iff,
    Sym2.eq_swap (a := u) (b := z),Sym2.eq_swap (a := z) (b := w),
    Sym2.eq_swap (a := w) (b := v),Sym2.eq_swap (a := v) (b := u)]
  tauto

omit [Fintype V] in
lemma square_edges_rotate (u v w z : V) :
    squareEdges v w z u = squareEdges u v w z := by
  ext e
  simp only [squareEdges,Set.mem_insert_iff,Set.mem_singleton_iff]
  tauto

lemma crossing_visits {a b u v w z : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwz : G.Adj w z) (hzu : G.Adj z u)
    (huw : u ≠ w) (hvz : v ≠ z)
    (A : G.Walk a u) (B : G.Walk u w) (C : G.Walk w v) (F : G.Walk v b)
    (hp : ((A.append B).append (C.append F)).IsPath) (hzF : z ∈ F.support)
    (hd : Disjoint ((A.append B).append (C.append F)).toSubgraph.edgeSet
      (squareEdges u v w z)) :
    TwoPathCover (G := G) (((A.append B).append (C.append F)).toSubgraph.edgeSet ∪
      squareEdges u v w z) := by
  cases C with
  | nil => exact (hvw.ne rfl).elim
  | @cons _ x _ h R =>
    have hform : F=(F.takeUntil z hzF).append (F.dropUntil z hzF) := (F.take_spec hzF).symm
    have hh := crossing_order huv hvw hwz hzu huw hvz A B h R
      (F.takeUntil z hzF) (F.dropUntil z hzF)
      (by simpa only [←hform,Walk.cons_append] using hp)
      (by simpa only [←hform,Walk.cons_append] using hd)
    simpa only [←hform,Walk.cons_append] using hh

lemma opposite_first {a b u v w z : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwz : G.Adj w z) (hzu : G.Adj z u)
    (huw : u ≠ w) (hvz : v ≠ z)
    (A : G.Walk a u) (B : G.Walk u w) (D : G.Walk w b)
    (hp : ((A.append B).append D).IsPath)
    (hvD : v ∈ D.support) (hzD : z ∈ D.support)
    (hd : Disjoint ((A.append B).append D).toSubgraph.edgeSet (squareEdges u v w z)) :
    TwoPathCover (G := G) (((A.append B).append D).toSubgraph.edgeSet ∪
      squareEdges u v w z) := by
  obtain ⟨q,hq,C,F,hform,hC⟩ := first_hit_split D ({v,z} : Set V) ⟨v,hvD,by simp⟩
  rcases (show q=v ∨ q=z by simpa using hq) with rfl|rfl
  · have hzF : z ∈ F.support := by
      rw [hform,Walk.mem_support_append_iff] at hzD
      exact hzD.elim (fun hh ↦ (hvz (hC z hh (by simp)).symm).elim) id
    have hh := crossing_visits huv hvw hwz hzu huw hvz A B C F
      (hform ▸ hp) hzF (hform ▸ hd)
    simpa only [←hform] using hh
  · have hvF : v ∈ F.support := by
      rw [hform,Walk.mem_support_append_iff] at hvD
      exact hvD.elim (fun hh ↦ (hvz (hC v hh (by simp))).elim) id
    have hh := crossing_visits hzu.symm hwz.symm hvw.symm huv.symm huw hvz.symm A B C F
      (hform ▸ hp) hvF (by simpa only [square_edges_reverse,←hform] using hd)
    simpa only [square_edges_reverse,←hform] using hh

/-- Absorb the quadrilateral after splitting at the first cycle vertex. -/
lemma absorb_at_first {a b u v w z : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwz : G.Adj w z) (hzu : G.Adj z u)
    (huw : u ≠ w) (hvz : v ≠ z)
    (A : G.Walk a u) (D : G.Walk u b) (hp : (A.append D).IsPath)
    (hvA : v ∉ A.support) (hwA : w ∉ A.support) (hzA : z ∉ A.support)
    (hd : Disjoint (A.append D).toSubgraph.edgeSet (squareEdges u v w z)) :
    TwoPathCover (G := G) ((A.append D).toSubgraph.edgeSet ∪ squareEdges u v w z) := by
  by_cases hvD : v ∈ D.support
  · by_cases hzD : z ∈ D.support
    · obtain ⟨q,hq,B,E,hform,hB⟩ := first_hit_split D ({v,w,z} : Set V) ⟨v,hvD,by simp⟩
      rcases (show q=v ∨ q=w ∨ q=z by simpa using hq) with rfl|rfl|rfl
      · cases B with
        | nil => exact (huv.ne rfl).elim
        | @cons _ x _ h R =>
          have hwR : w ∉ R.support := fun hh ↦
            hvw.ne (hB w (List.mem_cons_of_mem _ hh) (by simp)).symm
          have hzR : z ∉ R.support := fun hh ↦
            hvz (hB z (List.mem_cons_of_mem _ hh) (by simp)).symm
          have hh := adjacent_first huv hvw hwz hzu huw hvz A h R E
            (by simpa only [hform,Walk.cons_append] using hp) hvA hwA hzA hwR hzR
            (by simpa only [hform,Walk.cons_append] using hd)
          simpa only [hform,Walk.cons_append] using hh
      · have hvE : v ∈ E.support := by
          rw [hform,Walk.mem_support_append_iff] at hvD
          exact hvD.elim (fun hh ↦ (hvw.ne (hB v hh (by simp))).elim) id
        have hzE : z ∈ E.support := by
          rw [hform,Walk.mem_support_append_iff] at hzD
          exact hzD.elim (fun hh ↦ (hwz.ne (hB z hh (by simp)).symm).elim) id
        have hh := opposite_first huv hvw hwz hzu huw hvz A B E
          (by simpa only [hform,←Walk.append_assoc] using hp) hvE hzE
          (by simpa only [hform,←Walk.append_assoc] using hd)
        simpa only [hform,←Walk.append_assoc] using hh
      · cases B with
        | nil => exact (hzu.ne rfl).elim
        | @cons _ x _ h R =>
          have hwR : w ∉ R.support := fun hh ↦
            hwz.ne (hB w (List.mem_cons_of_mem _ hh) (by simp))
          have hvR : v ∉ R.support := fun hh ↦
            hvz (hB v (List.mem_cons_of_mem _ hh) (by simp))
          have hh := adjacent_first hzu.symm hwz.symm hvw.symm huv.symm huw hvz.symm A h R E
            (by simpa only [hform,Walk.cons_append] using hp) hzA hwA hvA hwR hvR
            (by simpa only [square_edges_reverse,hform,Walk.cons_append] using hd)
          simpa only [square_edges_reverse,hform,Walk.cons_append] using hh
    · have hh := missing_corner hzu.symm hwz.symm hvw.symm huv.symm huw hvz.symm
        A D hp hzA hwA hvA hzD (by simpa only [square_edges_reverse] using hd)
      simpa only [square_edges_reverse] using hh
  · exact missing_corner huv hvw hwz hzu huw hvz A D hp hvA hwA hzA hvD hd

/-- An edge-disjoint four-cycle and an intersecting simple path can always
be repartitioned into two simple paths. The old path may have arbitrary length. -/
lemma quadrilateral_path_absorption {a b u v w z : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwz : G.Adj w z) (hzu : G.Adj z u)
    (huw : u ≠ w) (hvz : v ≠ z)
    (P : G.Walk a b) (hp : P.IsPath)
    (hinter : ∃ x ∈ P.support, x ∈ ({u,v,w,z} : Set V))
    (hd : Disjoint P.toSubgraph.edgeSet (squareEdges u v w z)) :
    TwoPathCover (G := G) (P.toSubgraph.edgeSet ∪ squareEdges u v w z) := by
  obtain ⟨q,hq,A,D,hform,hA⟩ := first_hit_split P ({u,v,w,z} : Set V) hinter
  have hstep {s t d : V} (hqs : G.Adj q s) (hst : G.Adj s t)
      (htd : G.Adj t d) (hdq : G.Adj d q) (hqt : q ≠ t) (hsd : s ≠ d)
      (hV : ({q,s,t,d} : Set V)={u,v,w,z})
      (hE : squareEdges q s t d=squareEdges u v w z) :
      TwoPathCover (G := G) (P.toSubgraph.edgeSet ∪ squareEdges u v w z) := by
    have hsA : s ∉ A.support := fun hh ↦ hqs.ne (hA s hh (by rw [←hV]; simp)).symm
    have htA : t ∉ A.support := fun hh ↦ hqt (hA t hh (by rw [←hV]; simp)).symm
    have hdA : d ∉ A.support := fun hh ↦ hdq.ne (hA d hh (by rw [←hV]; simp))
    have hh := absorb_at_first hqs hst htd hdq hqt hsd A D (hform ▸ hp) hsA htA hdA
      (by simpa only [hE,←hform] using hd)
    simpa only [hE,←hform] using hh
  rcases (show q=u ∨ q=v ∨ q=w ∨ q=z by simpa using hq) with rfl|rfl|rfl|rfl
  · exact hstep huv hvw hwz hzu huw hvz rfl rfl
  · apply hstep hvw hwz hzu huv hvz huw.symm
    · ext x; simp only [Set.mem_insert_iff,Set.mem_singleton_iff]; tauto
    · exact square_edges_rotate _ _ _ _
  · apply hstep hwz hzu huv hvw huw.symm hvz.symm
    · ext x; simp only [Set.mem_insert_iff,Set.mem_singleton_iff]; tauto
    · exact (square_edges_rotate _ _ _ _).trans (square_edges_rotate _ _ _ _)
  · apply hstep hzu huv hvw hwz hvz.symm huw
    · ext x; simp only [Set.mem_insert_iff,Set.mem_singleton_iff]; tauto
    · exact (square_edges_rotate _ _ _ _).trans
        ((square_edges_rotate _ _ _ _).trans (square_edges_rotate _ _ _ _))

def squareWalk {u v w z : V} (huv : G.Adj u v) (hvw : G.Adj v w)
    (hwz : G.Adj w z) (hzu : G.Adj z u) : G.Walk u u :=
  .cons huv (.cons hvw (.cons hwz (.cons hzu .nil)))

omit [Fintype V] in
lemma square_isCycle {u v w z : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwz : G.Adj w z) (hzu : G.Adj z u)
    (huw : u ≠ w) (hvz : v ≠ z) : (squareWalk huv hvw hwz hzu).IsCycle := by
  simp [squareWalk,Walk.cons_isCycle_iff,Walk.isPath_def,huv.ne,hvw.ne,hwz.ne,hzu.ne,
    huw,hvz,huv.ne.symm,huw.symm]

omit [Fintype V] in
lemma squareWalk_edges {u v w z : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwz : G.Adj w z) (hzu : G.Adj z u) :
    (squareWalk huv hvw hwz hzu).toSubgraph.edgeSet=squareEdges u v w z := by
  ext e
  simp only [squareWalk,squareEdges,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_nil,
    List.mem_cons,List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff]

omit [Fintype V] in
lemma squareWalk_verts {u v w z : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwz : G.Adj w z) (hzu : G.Adj z u) :
    (squareWalk huv hvw hwz hzu).toSubgraph.verts=({u,v,w,z} : Set V) := by
  ext x
  simp only [squareWalk,Walk.mem_verts_toSubgraph,Walk.support_cons,Walk.support_nil,
    List.mem_cons,List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff]
  tauto

/-- Whole quadrilaterals cannot meet path members at a global score maximum. -/
lemma maximal_square_no_intersecting_path {k : ℕ} (T : TrailFamily G k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (i j : Fin k) (hij : i ≠ j) {u v w z : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwz : G.Adj w z) (hzu : G.Adj z u)
    (huw : u ≠ w) (hvz : v ≠ z)
    (hi : (T.walk i).toSubgraph=(squareWalk huv hvw hwz hzu).toSubgraph)
    (hj : (T.walk j).IsPath) :
    ¬∃ x ∈ (T.walk j).support, x ∈ ({u,v,w,z} : Set V) := by
  intro hinter
  have heS : (T.walk i).toSubgraph.edgeSet=squareEdges u v w z := by rw [hi,squareWalk_edges]
  have hdS : Disjoint (T.walk j).toSubgraph.edgeSet (squareEdges u v w z) := by
    rw [←heS]; exact T.disjoint hij.symm
  obtain ⟨a,b,c,d,X,Y,hX,hY,hd,he⟩ :=
    quadrilateral_path_absorption huv hvw hwz hzu huw hvz (T.walk j) hj hinter hdS
  have he' : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet =
      (T.walk i).toSubgraph.edgeSet ∪ (T.walk j).toSubgraph.edgeSet := by
    rw [he,heS,Set.union_comm]
  obtain ⟨U,_,_,_,hs⟩ := GeneralPair.replace_two T i j hij a b c d X Y
    hX.isTrail hY.isTrail hd he'
  have hlen : X.length+Y.length=(T.walk j).length+4 := by
    have hc := square_union_ncard huv hvw hwz hzu huw hvz (T.walk j) hj hdS
    rw [←he,Set.ncard_union_eq hd,trail_edgeSet_ncard X hX.isTrail,
      trail_edgeSet_ncard Y hY.isTrail] at hc
    exact hc
  have hi4 : (T.walk i).toSubgraph.verts.ncard=4 := by
    rw [hi,Walk.verts_toSubgraph,cycle_support_ncard (square_isCycle huv hvw hwz hzu huw hvz)]
    rfl
  rw [hi4,(walk_vertex_ncard_eq_iff (T.walk j)).mpr hj,
    (walk_vertex_ncard_eq_iff X).mpr hX,(walk_vertex_ncard_eq_iff Y).mpr hY] at hs
  have hb := hm U
  omega

/-- In a connected graph, a single-defect maximum with at least two slots
has no whole quadrilateral member. This does not exclude a lollipop prefix. -/
lemma maximal_single_defect_no_square {k : ℕ} (T : TrailFamily G k) (hG : G.Connected)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hk : 2 ≤ k)
    (i : Fin k) {u v w z : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwz : G.Adj w z) (hzu : G.Adj z u)
    (huw : u ≠ w) (hvz : v ≠ z) :
    (T.walk i).toSubgraph ≠ (squareWalk huv hvw hwz hzu).toSubgraph := by
  intro hi
  let S : Set V := {u,v,w,z}
  have hiv : (T.walk i).toSubgraph.verts=S := by rw [hi,squareWalk_verts]
  have hiNP := CycleEar.cycle_member_not_path T i _ (square_isCycle huv hvw hwz hzu huw hvz) hi
  have hother (j : Fin k) (hj : j ≠ i) : ¬∃ x ∈ (T.walk j).support, x ∈ S :=
    maximal_square_no_intersecting_path T hm i j hj.symm huv hvw hwz hzu huw hvz hi
      ((T.one_defect_other_paths hs i hiNP).2 j hj)
  have hS : S=Set.univ := by
    apply TrailBudget.connected_closed_set hG S ⟨u,by simp [S]⟩
    intro x y hxy hx
    obtain ⟨j,hj⟩ := (T.cover s(x,y)).mp hxy
    by_cases hji : j=i
    · subst j
      have hy : y ∈ (T.walk i).toSubgraph.verts :=
        (T.walk i).toSubgraph.edge_vert (show (T.walk i).toSubgraph.Adj y x from hj.symm)
      rwa [hiv] at hy
    · have hxj : x ∈ (T.walk j).support := (T.walk j).mem_verts_toSubgraph.mp
        ((T.walk j).toSubgraph.edge_vert (show (T.walk j).toSubgraph.Adj x y from hj))
      exact (hother j hji ⟨x,hxj,hx⟩).elim
  haveI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  obtain ⟨j,hji⟩ := exists_ne i
  exact hother j hji ⟨T.start j,(T.walk j).start_mem_support,by rw [hS]; trivial⟩

lemma budget_maximum_no_square {k : ℕ} (T : TrailFamily G k) (hG : G.Connected)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hk : Fintype.card V ≤ 2*k)
    (i : Fin k) {u v w z : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (hwz : G.Adj w z) (hzu : G.Adj z u)
    (huw : u ≠ w) (hvz : v ≠ z) :
    (T.walk i).toSubgraph ≠ (squareWalk huv hvw hwz hzu).toSubgraph := by
  have hc := Set.ncard_le_card (squareWalk huv hvw hwz hzu).toSubgraph.verts
  rw [Walk.verts_toSubgraph,cycle_support_ncard (square_isCycle huv hvw hwz hzu huw hvz)] at hc
  have hc' : 4 ≤ Fintype.card V := by
    change 4 ≤ Nat.card V at hc
    simpa only [Nat.card_eq_fintype_card] using hc
  exact maximal_single_defect_no_square T hG hs hm (by omega) i huv hvw hwz hzu huw hvz

omit [Fintype V] in
lemma three_cycle_rep {r : V} (C : G.Walk r r) (hl : C.length=3) :
    ∃ v w, ∃ hrv : G.Adj r v, ∃ hvw : G.Adj v w, ∃ hwr : G.Adj w r,
      C=Walk.cons hrv (Walk.cons hvw (Walk.cons hwr Walk.nil)) := by
  cases C with
  | nil => simp at hl
  | @cons _ v _ hrv P =>
    cases P with
    | nil => simp at hl
    | @cons _ w _ hvw Q =>
      cases Q with
      | nil => simp at hl
      | @cons _ x _ hwx R =>
        have hn : R.Nil := Walk.nil_iff_length_eq.mpr (by simp only [Walk.length_cons] at hl; omega)
        cases hn
        exact ⟨v,w,hrv,hvw,hwx,rfl⟩

omit [Fintype V] in
lemma four_cycle_rep {r : V} (C : G.Walk r r) (hc : C.IsCycle) (hl : C.length=4) :
    ∃ v w z, ∃ hrv : G.Adj r v, ∃ hvw : G.Adj v w, ∃ hwz : G.Adj w z,
      ∃ hzr : G.Adj z r, r ≠ w ∧ v ≠ z ∧ C=squareWalk hrv hvw hwz hzr := by
  cases C with
  | nil => simp at hl
  | @cons _ v _ hrv P =>
    cases P with
    | nil => simp at hl
    | @cons _ w _ hvw Q =>
      cases Q with
      | nil => simp at hl
      | @cons _ z _ hwz R =>
        cases R with
        | nil => simp at hl
        | @cons _ x _ hzx S =>
          have hn : S.Nil := Walk.nil_iff_length_eq.mpr (by simp only [Walk.length_cons] at hl; omega)
          cases hn
          have htail := (Walk.cons_isCycle_iff _ hrv).mp hc |>.1
          have hn : [v,w,z,r].Nodup := htail.support_nodup
          simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
          exact ⟨v,w,z,hrv,hvw,hwz,hzx,fun h ↦ hn.2.1.2 h.symm,hn.1.2.1,rfl⟩

/-- Any whole cycle at an exact-budget single-defect maximum has length
at least five. The five-cycle obstruction shows why local absorption alone
cannot be continued indiscriminately to larger cycles. -/
lemma whole_cycle_length_ge_five {k : ℕ} (T : TrailFamily G k) (hG : G.Connected)
    (hs : T.score+1=G.edgeSet.ncard+k)
    (hm : ∀ U : TrailFamily G k, U.score ≤ T.score) (hk : Fintype.card V ≤ 2*k)
    (i : Fin k) {r : V} (C : G.Walk r r) (hc : C.IsCycle)
    (hi : (T.walk i).toSubgraph=C.toSubgraph) : 5 ≤ C.length := by
  have h3 : C.length ≠ 3 := by
    intro hl
    obtain ⟨v,w,hrv,hvw,hwr,hC⟩ := three_cycle_rep C hl
    apply TriangleAbsorption.budget_maximum_no_triangle T hG hs hm hk i hrv hvw hwr.symm
    simpa only [hC] using hi
  have h4 : C.length ≠ 4 := by
    intro hl
    obtain ⟨v,w,z,hrv,hvw,hwz,hzr,hrw,hvz,hC⟩ := four_cycle_rep C hc hl
    exact budget_maximum_no_square T hG hs hm hk i hrv hvw hwz hzr hrw hvz (by rwa [←hC])
  have hmin := hc.three_le_length
  omega

end Erdos583QuadrilateralAbsorptionDevelopment
