import Submission.Work

/-! Exchanges for a triangle with a short attached tail. These lemmas do
not assert absorption for arbitrary long tails. -/
namespace Erdos583TriangleTailTwoDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery Erdos583Work.TriangleAbsorption
open scoped Classical
set_option maxHeartbeats 2000000

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
lemma triangle_tail_edges_card {r v w t b : V}
    (hrv : G.Adj r v) (hvw : G.Adj v w) (hrw : G.Adj r w)
    (hrt : G.Adj r t) (htb : G.Adj t b)
    (hbr : b ≠ r) (htv : t ≠ v) (htw : t ≠ w) (hbv : b ≠ v) (hbw : b ≠ w) :
    ({s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)} : Set (Sym2 V)).ncard=5 := by
  classical
  have hvr := hrv.ne.symm
  have hwr := hrw.ne.symm
  have htr := hrt.ne.symm
  have hbt := htb.ne.symm
  have hwv := hvw.ne.symm
  have h1 : s(r,v) ∉ ({s(v,w),s(r,w),s(r,t),s(t,b)} : Set (Sym2 V)) := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_iff]
    aesop
  have h2 : s(v,w) ∉ ({s(r,w),s(r,t),s(t,b)} : Set (Sym2 V)) := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_iff]
    aesop
  have h3 : s(r,w) ∉ ({s(r,t),s(t,b)} : Set (Sym2 V)) := by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_iff]
    aesop
  have h4 : s(r,t) ∉ ({s(t,b)} : Set (Sym2 V)) := by
    simp only [Set.mem_singleton_iff,Sym2.eq_iff]
    aesop
  rw [Set.ncard_insert_of_notMem h1,Set.ncard_insert_of_notMem h2,
    Set.ncard_insert_of_notMem h3,Set.ncard_insert_of_notMem h4,Set.ncard_singleton]


lemma triangle_tail_union_card {r v w t b a d : V}
    (hrv : G.Adj r v) (hvw : G.Adj v w) (hrw : G.Adj r w)
    (hrt : G.Adj r t) (htb : G.Adj t b)
    (hbr : b ≠ r) (htv : t ≠ v) (htw : t ≠ w) (hbv : b ≠ v) (hbw : b ≠ w)
    (P : G.Walk a d) (hp : P.IsPath)
    (hd : Disjoint P.toSubgraph.edgeSet {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) :
    (P.toSubgraph.edgeSet ∪ {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}).ncard=P.length+5 := by
  rw [Set.ncard_union_eq hd,trail_edgeSet_ncard P hp.isTrail,
    triangle_tail_edges_card hrv hvw hrw hrt htb hbr htv htw hbv hbw]

/-- If the triangle is visited after both tails of a chosen prefix have
been excluded, attach the entire two-edge tail to that prefix path. -/
lemma tail_before_triangle_prefix {r v w t b a d : V}
    (hrv : G.Adj r v) (hvw : G.Adj v w) (hrw : G.Adj r w)
    (hrt : G.Adj r t) (htb : G.Adj t b)
    (hbr : b ≠ r) (htv : t ≠ v) (htw : t ≠ w) (hbv : b ≠ v) (hbw : b ≠ w)
    (A : G.Walk a w) (D : G.Walk w d) (hp : (A.append D).IsPath)
    (hr : r ∉ (A.append D).support) (hvA : v ∉ A.support)
    (htA : t ∉ A.support) (hbA : b ∉ A.support)
    (hd : Disjoint (A.append D).toSubgraph.edgeSet {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) :
    TwoPathCover (G := G) ((A.append D).toSubgraph.edgeSet ∪
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) := by
  let X := Walk.cons htb.symm (Walk.cons hrt.symm (Walk.cons hrv (Walk.cons hvw A.reverse)))
  let Y := Walk.cons hrw D
  have hrA : r ∉ A.support := fun hx ↦ hr ((Walk.mem_support_append_iff A D).mpr (Or.inl hx))
  have hrD : r ∉ D.support := fun hx ↦ hr ((Walk.mem_support_append_iff A D).mpr (Or.inr hx))
  have hX : X.IsPath := by
    simp only [X,Walk.cons_isPath_iff,Walk.support_cons,Walk.support_reverse,List.mem_cons,List.mem_reverse,not_or]
    exact ⟨⟨⟨⟨hp.of_append_left.reverse,hvA⟩,hrv.ne,hrA⟩,
      hrt.ne.symm,htv,htA⟩,htb.ne.symm,hbr,hbv,hbA⟩
  have hY : Y.IsPath := (Walk.cons_isPath_iff hrw D).mpr ⟨hp.of_append_right,hrD⟩
  have he : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=(A.append D).toSubgraph.edgeSet ∪
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)} := by
    ext e
    simp only [X,Y,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_reverse,Walk.edges_append,
      List.mem_cons,List.mem_reverse,List.mem_append,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,
      Sym2.eq_swap (a := b) (b := t),Sym2.eq_swap (a := t) (b := r)]
    tauto
  have hc : X.length+Y.length=((A.append D).toSubgraph.edgeSet ∪
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}).ncard := by
    rw [triangle_tail_union_card hrv hvw hrw hrt htb hbr htv htw hbv hbw _ hp hd]
    simp [X,Y]
    omega
  exact ⟨b,a,r,d,X,Y,hX,hY,disjoint_of_cover_length X Y hX.isTrail hY.isTrail _ he hc,he⟩

lemma tail_before_triangle_last {r v w t b a d : V}
    (hrv : G.Adj r v) (hvw : G.Adj v w) (hrw : G.Adj r w)
    (hrt : G.Adj r t) (htb : G.Adj t b)
    (hbr : b ≠ r) (htv : t ≠ v) (htw : t ≠ w) (hbv : b ≠ v) (hbw : b ≠ w)
    (A : G.Walk a w) (D : G.Walk w d) (hp : (A.append D).IsPath)
    (hr : r ∉ (A.append D).support) (hvD : v ∉ D.support)
    (htA : t ∉ A.support) (hbA : b ∉ A.support)
    (hd : Disjoint (A.append D).toSubgraph.edgeSet {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) :
    TwoPathCover (G := G) ((A.append D).toSubgraph.edgeSet ∪
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) := by
  let X := Walk.cons htb.symm (Walk.cons hrt.symm (Walk.cons hrw A.reverse))
  let Y := Walk.cons hrv (Walk.cons hvw D)
  have hrA : r ∉ A.support := fun hx ↦ hr ((Walk.mem_support_append_iff A D).mpr (Or.inl hx))
  have hrD : r ∉ D.support := fun hx ↦ hr ((Walk.mem_support_append_iff A D).mpr (Or.inr hx))
  have hX : X.IsPath := by
    simp only [X,Walk.cons_isPath_iff,Walk.support_cons,Walk.support_reverse,List.mem_cons,List.mem_reverse,not_or]
    exact ⟨⟨⟨hp.of_append_left.reverse,hrA⟩,hrt.ne.symm,htA⟩,htb.ne.symm,hbr,hbA⟩
  have hY : Y.IsPath := by
    simp only [Y,Walk.cons_isPath_iff,Walk.support_cons,List.mem_cons,not_or]
    exact ⟨⟨hp.of_append_right,hvD⟩,hrv.ne,hrD⟩
  have he : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=(A.append D).toSubgraph.edgeSet ∪
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)} := by
    ext e
    simp only [X,Y,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_reverse,Walk.edges_append,
      List.mem_cons,List.mem_reverse,List.mem_append,Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,
      Sym2.eq_swap (a := b) (b := t),Sym2.eq_swap (a := t) (b := r)]
    tauto
  have hc : X.length+Y.length=((A.append D).toSubgraph.edgeSet ∪
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}).ncard := by
    rw [triangle_tail_union_card hrv hvw hrw hrt htb hbr htv htw hbv hbw _ hp hd]
    simp [X,Y]
    omega
  exact ⟨b,a,r,d,X,Y,hX,hY,disjoint_of_cover_length X Y hX.isTrail hY.isTrail _ he hc,he⟩

/-- The remaining ordering has the two tail vertices on opposite sides of
all triangle visits. The tail edge joins the two sides after the exchange. -/
lemma tail_brackets_triangle {r v w t b a d : V}
    (hrv : G.Adj r v) (hvw : G.Adj v w) (hrw : G.Adj r w)
    (hrt : G.Adj r t) (htb : G.Adj t b)
    (hbr : b ≠ r) (htv : t ≠ v) (htw : t ≠ w) (hbv : b ≠ v) (hbw : b ≠ w)
    (A : G.Walk a t) (B : G.Walk t w) (D : G.Walk w d)
    (hp : ((A.append B).append D).IsPath) (hbD : b ∈ D.support)
    (hr : r ∉ ((A.append B).append D).support)
    (hvA : v ∉ A.support) (hvD : v ∉ D.support)
    (hd : Disjoint ((A.append B).append D).toSubgraph.edgeSet {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) :
    TwoPathCover (G := G) (((A.append B).append D).toSubgraph.edgeSet ∪
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) := by
  have hAB := hp.of_append_left
  have hBD : (B.append D).IsPath := by rw [←Walk.append_assoc] at hp; exact hp.of_append_right
  have hrA : r ∉ A.support := fun hx ↦ hr (by simp only [Walk.mem_support_append_iff]; exact Or.inl (Or.inl hx))
  have hrB : r ∉ B.support := fun hx ↦ hr (by simp only [Walk.mem_support_append_iff]; exact Or.inl (Or.inr hx))
  have hrD : r ∉ D.support := fun hx ↦ hr (by simp only [Walk.mem_support_append_iff]; exact Or.inr hx)
  have hbB : b ∉ B.support := fun hx ↦ (hBD.ne_of_mem_support_of_append hbw hx hbD) rfl
  have htD : t ∉ D.support := fun hx ↦ (hBD.ne_of_mem_support_of_append htw B.start_mem_support hx) rfl
  have hwA : w ∉ A.support := fun hx ↦ (hAB.ne_of_mem_support_of_append htw.symm hx B.end_mem_support) rfl
  let Q := Walk.cons hrt.symm (Walk.cons hrv (Walk.cons hvw D))
  have hQ : Q.IsPath := by
    simp only [Q,Walk.cons_isPath_iff,Walk.support_cons,List.mem_cons,not_or]
    exact ⟨⟨⟨hp.of_append_right,hvD⟩,hrv.ne,hrD⟩,hrt.ne.symm,htv,htD⟩
  let X := A.append Q
  have hX : X.IsPath := path_append_of_support_intersection hAB.of_append_left hQ (by
    intro z hzA hzQ
    simp only [Q,Walk.support_cons,List.mem_cons] at hzQ
    rcases hzQ with rfl|rfl|rfl|hzD
    · rfl
    · exact (hrA hzA).elim
    · exact (hvA hzA).elim
    · by_contra hzt
      exact (show (A.append (B.append D)).IsPath by rwa [Walk.append_assoc]).ne_of_mem_support_of_append
        hzt hzA ((Walk.mem_support_append_iff B D).mpr (Or.inr hzD)) rfl)
  let Y := Walk.cons hrw (B.reverse.concat htb)
  have hY : Y.IsPath := (Walk.cons_isPath_iff hrw _).mpr ⟨hAB.of_append_right.reverse.concat
    (by simpa only [Walk.support_reverse,List.mem_reverse] using hbB) htb,by
      simp only [Walk.support_concat,Walk.support_reverse,List.concat_eq_append,List.mem_append,List.mem_reverse,List.mem_singleton,not_or]
      exact ⟨hrB,hbr.symm⟩⟩
  have he : X.toSubgraph.edgeSet ∪ Y.toSubgraph.edgeSet=((A.append B).append D).toSubgraph.edgeSet ∪
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)} := by
    ext e
    simp only [X,Y,Q,Walk.mem_edges_toSubgraph,Walk.edges_cons,Walk.edges_concat,Walk.edges_reverse,Walk.edges_append,
      List.mem_cons,List.mem_reverse,List.mem_append,List.concat_eq_append,
      Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := t) (b := r)]
    tauto
  have hc : X.length+Y.length=(((A.append B).append D).toSubgraph.edgeSet ∪
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}).ncard := by
    rw [triangle_tail_union_card hrv hvw hrw hrt htb hbr htv htw hbv hbw _ hp hd]
    simp [X,Y,Q]
    omega
  exact ⟨a,d,r,b,X,Y,hX,hY,disjoint_of_cover_length X Y hX.isTrail hY.isTrail _ he hc,he⟩


lemma tail_avoids_prefix {r v w t b a d : V}
    (hrv : G.Adj r v) (hvw : G.Adj v w) (hrw : G.Adj r w)
    (hrt : G.Adj r t) (htb : G.Adj t b)
    (hbr : b ≠ r) (htv : t ≠ v) (htw : t ≠ w) (hbv : b ≠ v) (hbw : b ≠ w)
    (A : G.Walk a w) (D : G.Walk w d) (hp : (A.append D).IsPath)
    (hr : r ∉ (A.append D).support) (htA : t ∉ A.support) (hbA : b ∉ A.support)
    (hd : Disjoint (A.append D).toSubgraph.edgeSet {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) :
    TwoPathCover (G := G) ((A.append D).toSubgraph.edgeSet ∪
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) := by
  by_cases hvA : v ∈ A.support
  · have hvD : v ∉ D.support := fun h ↦ (hp.ne_of_mem_support_of_append hvw.ne hvA h) rfl
    exact tail_before_triangle_last hrv hvw hrw hrt htb hbr htv htw hbv hbw A D hp hr hvD htA hbA hd
  · exact tail_before_triangle_prefix hrv hvw hrw hrt htb hbr htv htw hbv hbw A D hp hr hvA htA hbA hd

lemma tail_avoids_suffix {r v w t b a d : V}
    (hrv : G.Adj r v) (hvw : G.Adj v w) (hrw : G.Adj r w)
    (hrt : G.Adj r t) (htb : G.Adj t b)
    (hbr : b ≠ r) (htv : t ≠ v) (htw : t ≠ w) (hbv : b ≠ v) (hbw : b ≠ w)
    (A : G.Walk a w) (D : G.Walk w d) (hp : (A.append D).IsPath)
    (hr : r ∉ (A.append D).support) (htD : t ∉ D.support) (hbD : b ∉ D.support)
    (hd : Disjoint (A.append D).toSubgraph.edgeSet {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) :
    TwoPathCover (G := G) ((A.append D).toSubgraph.edgeSet ∪
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) := by
  have he : (D.reverse.append A.reverse)=(A.append D).reverse := (Walk.reverse_append A D).symm
  have hh := tail_avoids_prefix hrv hvw hrw hrt htb hbr htv htw hbv hbw D.reverse A.reverse
    (by rw [he]; exact hp.reverse) (by simpa only [he,Walk.support_reverse,List.mem_reverse] using hr)
    (by simpa only [Walk.support_reverse,List.mem_reverse] using htD)
    (by simpa only [Walk.support_reverse,List.mem_reverse] using hbD)
    (by simpa only [he,Walk.toSubgraph_reverse] using hd)
  simpa only [he,Walk.toSubgraph_reverse] using hh

omit [Fintype V] in
lemma triangle_tail_edges_swap (r v w t b : V) :
    ({s(r,w),s(w,v),s(r,v),s(r,t),s(t,b)} : Set (Sym2 V))=
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)} := by
  ext e
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := w) (b := v)]
  tauto

lemma tail_missing_vertex_absorption {r v w t b a d : V}
    (hrv : G.Adj r v) (hvw : G.Adj v w) (hrw : G.Adj r w)
    (hrt : G.Adj r t) (htb : G.Adj t b)
    (hbr : b ≠ r) (htv : t ≠ v) (htw : t ≠ w) (hbv : b ≠ v) (hbw : b ≠ w)
    (P : G.Walk a d) (hp : P.IsPath) (hr : r ∉ P.support)
    (hw : w ∈ P.support) (hmiss : t ∉ P.support ∨ b ∉ P.support)
    (hd : Disjoint P.toSubgraph.edgeSet {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) :
    TwoPathCover (G := G) (P.toSubgraph.edgeSet ∪
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) := by
  obtain ⟨A,D,hform⟩ := P.mem_support_iff_exists_append.mp hw
  rw [hform] at hp hr hd hmiss ⊢
  by_cases htA : t ∈ A.support
  · have htD : t ∉ D.support := fun h ↦ (hp.ne_of_mem_support_of_append htw htA h) rfl
    have hbP : b ∉ (A.append D).support := hmiss.resolve_left
      (fun h ↦ h ((Walk.mem_support_append_iff A D).mpr (Or.inl htA)))
    exact tail_avoids_suffix hrv hvw hrw hrt htb hbr htv htw hbv hbw A D hp hr htD
      (fun h ↦ hbP ((Walk.mem_support_append_iff A D).mpr (Or.inr h))) hd
  · by_cases hbA : b ∈ A.support
    · have hbD : b ∉ D.support := fun h ↦ (hp.ne_of_mem_support_of_append hbw hbA h) rfl
      have htP : t ∉ (A.append D).support := hmiss.resolve_right
        (fun h ↦ h ((Walk.mem_support_append_iff A D).mpr (Or.inl hbA)))
      exact tail_avoids_suffix hrv hvw hrw hrt htb hbr htv htw hbv hbw A D hp hr
        (fun h ↦ htP ((Walk.mem_support_append_iff A D).mpr (Or.inr h))) hbD hd
    · exact tail_avoids_prefix hrv hvw hrw hrt htb hbr htv htw hbv hbw A D hp hr htA hbA hd

/-- A triangle visit before the first of the two tail vertices already
suffices for absorption. -/
lemma triangle_before_tail {r v w t b a c d : V}
    (hrv : G.Adj r v) (hvw : G.Adj v w) (hrw : G.Adj r w)
    (hrt : G.Adj r t) (htb : G.Adj t b)
    (hbr : b ≠ r) (htv : t ≠ v) (htw : t ≠ w) (hbv : b ≠ v) (hbw : b ≠ w)
    (A : G.Walk a c) (D : G.Walk c d) (hp : (A.append D).IsPath)
    (hr : r ∉ (A.append D).support) (hc : c=t ∨ c=b)
    (hA : ∀ z ∈ A.support, z=t ∨ z=b → z=c) (hw : w ∈ A.support)
    (hd : Disjoint (A.append D).toSubgraph.edgeSet {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) :
    TwoPathCover (G := G) ((A.append D).toSubgraph.edgeSet ∪
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) := by
  obtain ⟨E,F,hform⟩ := A.mem_support_iff_exists_append.mp hw
  have hE : ∀ z, z=t ∨ z=b → z ∉ E.support := by
    intro z hz hzE
    have hzc : z=c := hA z (by rw [hform,Walk.mem_support_append_iff]; exact Or.inl hzE) hz
    have hcw : c ≠ w := by rcases hc with rfl|rfl <;> assumption
    have hEF : (E.append F).IsPath := hform ▸ hp.of_append_left
    exact (hEF.ne_of_mem_support_of_append hcw (hzc ▸ hzE) F.end_mem_support) rfl
  have hPf : A.append D=E.append (F.append D) := by rw [hform,Walk.append_assoc]
  rw [hPf] at hp hr hd ⊢
  exact tail_avoids_prefix hrv hvw hrw hrt htb hbr htv htw hbv hbw E (F.append D)
    hp hr (hE t (Or.inl rfl)) (hE b (Or.inr rfl)) hd


lemma triangle_before_tail_either {r v w t b a c d : V}
    (hrv : G.Adj r v) (hvw : G.Adj v w) (hrw : G.Adj r w)
    (hrt : G.Adj r t) (htb : G.Adj t b)
    (hbr : b ≠ r) (htv : t ≠ v) (htw : t ≠ w) (hbv : b ≠ v) (hbw : b ≠ w)
    (A : G.Walk a c) (D : G.Walk c d) (hp : (A.append D).IsPath)
    (hr : r ∉ (A.append D).support) (hc : c=t ∨ c=b)
    (hA : ∀ z ∈ A.support, z=t ∨ z=b → z=c)
    (htri : v ∈ A.support ∨ w ∈ A.support)
    (hd : Disjoint (A.append D).toSubgraph.edgeSet {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) :
    TwoPathCover (G := G) ((A.append D).toSubgraph.edgeSet ∪
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) := by
  rcases htri with hv|hw
  · have hh := triangle_before_tail hrw hvw.symm hrv hrt htb hbr htw htv hbw hbv A D hp hr hc hA hv
      (by simpa only [triangle_tail_edges_swap] using hd)
    simpa only [triangle_tail_edges_swap] using hh
  · exact triangle_before_tail hrv hvw hrw hrt htb hbr htv htw hbv hbw A D hp hr hc hA hw hd

lemma triangle_after_tail_either {r v w t b a c d : V}
    (hrv : G.Adj r v) (hvw : G.Adj v w) (hrw : G.Adj r w)
    (hrt : G.Adj r t) (htb : G.Adj t b)
    (hbr : b ≠ r) (htv : t ≠ v) (htw : t ≠ w) (hbv : b ≠ v) (hbw : b ≠ w)
    (A : G.Walk a c) (D : G.Walk c d) (hp : (A.append D).IsPath)
    (hr : r ∉ (A.append D).support) (hc : c=t ∨ c=b)
    (hD : ∀ z ∈ D.support, z=t ∨ z=b → z=c)
    (htri : v ∈ D.support ∨ w ∈ D.support)
    (hd : Disjoint (A.append D).toSubgraph.edgeSet {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) :
    TwoPathCover (G := G) ((A.append D).toSubgraph.edgeSet ∪
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) := by
  have he : D.reverse.append A.reverse=(A.append D).reverse := (Walk.reverse_append A D).symm
  have hh := triangle_before_tail_either hrv hvw hrw hrt htb hbr htv htw hbv hbw D.reverse A.reverse
    (by rw [he]; exact hp.reverse) (by simpa only [he,Walk.support_reverse,List.mem_reverse] using hr)
    hc (by simpa only [Walk.support_reverse,List.mem_reverse] using hD)
    (by simpa only [Walk.support_reverse,List.mem_reverse] using htri)
    (by simpa only [he,Walk.toSubgraph_reverse] using hd)
  simpa only [he,Walk.toSubgraph_reverse] using hh

lemma triangle_tail_two_ordered {r v w t b a d : V}
    (hrv : G.Adj r v) (hvw : G.Adj v w) (hrw : G.Adj r w)
    (hrt : G.Adj r t) (htb : G.Adj t b)
    (hbr : b ≠ r) (htv : t ≠ v) (htw : t ≠ w) (hbv : b ≠ v) (hbw : b ≠ w)
    (A : G.Walk a t) (B : G.Walk t b) (D : G.Walk b d)
    (hp : ((A.append B).append D).IsPath)
    (hr : r ∉ ((A.append B).append D).support)
    (htri : v ∈ ((A.append B).append D).support ∨ w ∈ ((A.append B).append D).support)
    (hd : Disjoint ((A.append B).append D).toSubgraph.edgeSet {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) :
    TwoPathCover (G := G) (((A.append B).append D).toSubgraph.edgeSet ∪
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) := by
  classical
  have hp' : (A.append (B.append D)).IsPath := by rwa [Walk.append_assoc]
  have hbA : b ∉ A.support := fun h ↦ (hp'.ne_of_mem_support_of_append htb.ne.symm h
    ((Walk.mem_support_append_iff B D).mpr (Or.inl B.end_mem_support))) rfl
  have htD : t ∉ D.support := fun h ↦ (hp.ne_of_mem_support_of_append htb.ne
    ((Walk.mem_support_append_iff A B).mpr (Or.inr B.start_mem_support)) h) rfl
  by_cases hA : v ∈ A.support ∨ w ∈ A.support
  · have hh := triangle_before_tail_either hrv hvw hrw hrt htb hbr htv htw hbv hbw A (B.append D) hp'
      (by rwa [Walk.append_assoc]) (Or.inl rfl) (by
        intro z hz hzt
        rcases hzt with rfl|rfl
        · rfl
        · exact (hbA hz).elim) hA (by rwa [Walk.append_assoc])
    simpa only [Walk.append_assoc] using hh
  by_cases hD : v ∈ D.support ∨ w ∈ D.support
  · exact triangle_after_tail_either hrv hvw hrw hrt htb hbr htv htw hbv hbw (A.append B) D hp hr
      (Or.inr rfl) (by
        intro z hz hzb
        rcases hzb with rfl|rfl
        · exact (htD hz).elim
        · rfl) hD hd
  have hvA : v ∉ A.support := fun h ↦ hA (Or.inl h)
  have hwA : w ∉ A.support := fun h ↦ hA (Or.inr h)
  have hvD : v ∉ D.support := fun h ↦ hD (Or.inl h)
  have hwD : w ∉ D.support := fun h ↦ hD (Or.inr h)
  have hhit : ∃ z ∈ B.support, z ∈ ({v,w} : Set V) := by
    simp only [Walk.mem_support_append_iff] at htri
    rcases htri with ((h|h)|h)|((h|h)|h)
    · exact (hvA h).elim
    · exact ⟨v,h,Or.inl rfl⟩
    · exact (hvD h).elim
    · exact (hwA h).elim
    · exact ⟨w,h,Or.inr rfl⟩
    · exact (hwD h).elim
  obtain ⟨z,hz,C,E,hform,hE⟩ := CycleDefect.last_hit_split B {v,w} hhit
  have heq : (A.append B).append D=(A.append C).append (E.append D) := by
    simp only [hform,Walk.append_assoc]
  rw [heq] at hp hr hd ⊢
  have hbED : b ∈ (E.append D).support := (Walk.mem_support_append_iff E D).mpr (Or.inl E.end_mem_support)
  rcases hz with hz|hz
  · have hz : z=v := hz
    subst z
    have hwED : w ∉ (E.append D).support := by
      intro h
      rcases (Walk.mem_support_append_iff E D).mp h with h|h
      · exact hvw.ne.symm (hE w h (Or.inr rfl))
      · exact hwD h
    have hh := tail_brackets_triangle hrw hvw.symm hrv hrt htb hbr htw htv hbw hbv A C (E.append D)
      hp hbED hr hwA hwED (by simpa only [triangle_tail_edges_swap] using hd)
    simpa only [triangle_tail_edges_swap] using hh
  · have hz : z=w := hz
    subst z
    have hvED : v ∉ (E.append D).support := by
      intro h
      rcases (Walk.mem_support_append_iff E D).mp h with h|h
      · exact hvw.ne (hE v h (Or.inl rfl))
      · exact hvD h
    exact tail_brackets_triangle hrv hvw hrw hrt htb hbr htv htw hbv hbw A C (E.append D)
      hp hbED hr hvA hvED hd

omit [Fintype V] in
lemma two_visits_oriented {a d t b : V} (P : G.Walk a d) (hp : P.IsPath)
    (ht : t ∈ P.support) (hb : b ∈ P.support) :
    ∃ c e, ∃ Q : G.Walk c e, Q.IsPath ∧ Q.toSubgraph=P.toSubgraph ∧
      ∃ A : G.Walk c t, ∃ B : G.Walk t b, ∃ D : G.Walk b e, Q=(A.append B).append D := by
  classical
  obtain ⟨A,R,hP⟩ := P.mem_support_iff_exists_append.mp ht
  by_cases hbR : b ∈ R.support
  · obtain ⟨B,D,hR⟩ := R.mem_support_iff_exists_append.mp hbR
    exact ⟨a,d,P,hp,rfl,A,B,D,by rw [hP,hR,Walk.append_assoc]⟩
  · have hbA : b ∈ A.support := ((Walk.mem_support_append_iff A R).mp (hP ▸ hb)).resolve_right hbR
    obtain ⟨E,F,hA⟩ := A.mem_support_iff_exists_append.mp hbA
    refine ⟨d,a,P.reverse,hp.reverse,by simp,R.reverse,F.reverse,E.reverse,?_⟩
    rw [hP,hA,Walk.reverse_append,Walk.reverse_append,Walk.append_assoc]

/-- A triangle with a two-edge tail can be absorbed against every
edge-disjoint path that avoids its root and meets another triangle vertex. -/
lemma triangle_tail_two_absorption {r v w t b a d : V}
    (hrv : G.Adj r v) (hvw : G.Adj v w) (hrw : G.Adj r w)
    (hrt : G.Adj r t) (htb : G.Adj t b)
    (hbr : b ≠ r) (htv : t ≠ v) (htw : t ≠ w) (hbv : b ≠ v) (hbw : b ≠ w)
    (P : G.Walk a d) (hp : P.IsPath) (hr : r ∉ P.support)
    (htri : v ∈ P.support ∨ w ∈ P.support)
    (hd : Disjoint P.toSubgraph.edgeSet {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) :
    TwoPathCover (G := G) (P.toSubgraph.edgeSet ∪
      {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)}) := by
  classical
  by_cases hboth : t ∈ P.support ∧ b ∈ P.support
  · obtain ⟨c,e,Q,hQ,hQe,A,B,D,hform⟩ := two_visits_oriented P hp hboth.1 hboth.2
    have hsup (z : V) : z ∈ Q.support ↔ z ∈ P.support := by
      rw [←Walk.mem_verts_toSubgraph,hQe,Walk.mem_verts_toSubgraph]
    have hQR : r ∉ Q.support := fun h ↦ hr ((hsup r).mp h)
    have hQT : v ∈ Q.support ∨ w ∈ Q.support := htri.imp (hsup v).mpr (hsup w).mpr
    have hQD : Disjoint Q.toSubgraph.edgeSet {s(r,v),s(v,w),s(r,w),s(r,t),s(t,b)} := by rwa [hQe]
    have hh := triangle_tail_two_ordered hrv hvw hrw hrt htb hbr htv htw hbv hbw A B D
      (hform ▸ hQ) (hform ▸ hQR) (hform ▸ hQT) (hform ▸ hQD)
    rwa [←hform,hQe] at hh
  · have hmiss : t ∉ P.support ∨ b ∉ P.support := not_and_or.mp hboth
    rcases htri with hv|hw
    · have hh := tail_missing_vertex_absorption hrw hvw.symm hrv hrt htb hbr htw htv hbw hbv P hp hr hv hmiss
        (by simpa only [triangle_tail_edges_swap] using hd)
      simpa only [triangle_tail_edges_swap] using hh
    · exact tail_missing_vertex_absorption hrv hvw hrw hrt htb hbr htv htw hbv hbw P hp hr hw hmiss hd


omit [Fintype V] in
lemma two_edge_form {r b : V} (P : G.Walk r b) (hlen : P.length=2) :
    ∃ t, ∃ hrt : G.Adj r t, ∃ htb : G.Adj t b, P=Walk.cons hrt (Walk.cons htb Walk.nil) := by
  cases P with
  | nil => simp at hlen
  | cons h P =>
    cases P with
    | nil => simp at hlen
    | cons h' P =>
      cases P with
      | nil => exact ⟨_,h,h',rfl⟩
      | cons h'' P => simp only [Walk.length_cons] at hlen; omega

lemma maximum_two_tail_triangle_no_outside_intersection {k : ℕ} (T : TrailFamily G k)
    (r : V) (L : LollipopEar.RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hcycle : L.cycle.length=3) (htail : L.tail.length=2)
    (j : Fin k) (hij : L.index ≠ j) (hr : r ∉ (T.walk j).support)
    (hinter : ∃ x ∈ L.cycle.support, x ∈ (T.walk j).support) : False := by
  obtain ⟨x,y,hrx,hxy,hyr,hC⟩ := QuadrilateralAbsorption.three_cycle_rep L.cycle hcycle
  obtain ⟨t,hrt,htb,hS⟩ := two_edge_form L.tail htail
  have hxC : x ∈ L.cycle.support := by rw [hC]; simp
  have hyC : y ∈ L.cycle.support := by rw [hC]; simp
  have htS : t ∈ L.tail.support := by rw [hS]; simp
  have hbS : L.finish ∈ L.tail.support := L.tail.end_mem_support
  have htx : t ≠ x := by intro he; exact hrx.ne (L.inter x hxC (he ▸ htS)).symm
  have hty : t ≠ y := by intro he; exact hyr.ne (L.inter y hyC (he ▸ htS))
  have hbx : L.finish ≠ x := by intro he; exact hrx.ne (L.inter x hxC (he ▸ hbS)).symm
  have hby : L.finish ≠ y := by intro he; exact hyr.ne (L.inter y hyC (he ▸ hbS))
  have hbr : L.finish ≠ r := by
    intro he
    have hh := (Walk.cons_isPath_iff hrt _).mp (hS ▸ L.isPath) |>.2
    exact hh (by simp [he])
  have hp := (T.one_defect_other_paths hs L.index L.member_not_path).2 j hij.symm
  have hhits : x ∈ (T.walk j).support ∨ y ∈ (T.walk j).support := by
    obtain ⟨z,hz,hzj⟩ := hinter
    rw [hC] at hz
    simp only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl
    · exact (hr hzj).elim
    · exact Or.inl hzj
    · exact Or.inr hzj
    · exact (hr hzj).elim
  have he : (T.walk L.index).toSubgraph.edgeSet=
      {s(r,x),s(x,y),s(r,y),s(r,t),s(t,L.finish)} := by
    rw [L.subgraph,hC,hS]
    ext e
    simp only [Walk.mem_edges_toSubgraph,Walk.edges_append,Walk.edges_cons,Walk.edges_nil,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
      Set.mem_insert_iff,Set.mem_singleton_iff,Sym2.eq_swap (a := y) (b := r)]
    tauto
  have hd : Disjoint (T.walk j).toSubgraph.edgeSet
      {s(r,x),s(x,y),s(r,y),s(r,t),s(t,L.finish)} := by
    rw [←he]
    exact T.disjoint hij.symm
  have hh := triangle_tail_two_absorption hrx hxy hyr.symm hrt htb hbr htx hty hbx hby
    (T.walk j) hp hr hhits hd
  apply ShortLollipop.maximum_one_defect_no_two_path_cover T hs hm L.index j hij L.member_not_path
  rw [he,Set.union_comm]
  exact hh

lemma cubic_triangle_tail_length_ge_three {n k : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (T : TrailFamily G k) (r : Fin n) (L : LollipopEar.RootedCycleRep T r)
    (hs : T.score+1=G.edgeSet.ncard+k) (hm : ∀ U : TrailFamily G k, U.score ≤ T.score)
    (hd : Nat.card (G.neighborSet r)=3) (hq : T.quota r ≤ 2) (hcycle : L.cycle.length=3) :
    3 ≤ L.tail.length := by
  have hq1 : T.quota r=1 := (QuotaParity.small_root_quota_one_iff T L.hasRoot hq).mpr (by rw [hd]; decide)
  have htwo := ShortLollipop.cubic_triangle_tail_length_ge_two hsmall hG hfail T r L hs hm hd hq hcycle
  by_contra hn
  have htail : L.tail.length=2 := by omega
  obtain ⟨x,y,hrx,hxy,hyr,hC⟩ := QuadrilateralAbsorption.three_cycle_rep L.cycle hcycle
  have hxC : x ∈ L.cycle.support := by rw [hC]; simp
  have hx2 := NormalRemainder.cycle_degree_ge_two L.cycle L.isCycle hxC
  have hx3 : 3 ≤ Nat.card (G.neighborSet x) := by
    by_contra hn
    have hxdeg : Nat.card (G.neighborSet x)=2 := by omega
    have hh := LowDegreeAdjacency.degree_two_neighbors_ge_four hsmall hG hfail hrx.symm hxdeg
    omega
  have hxN : x ∈ (MemberExpansion.selectedGraph T (Finset.univ.erase L.index)).support := by
    by_contra hx
    have hh := TailEar.missing_normal_degree_bound T r L hs hm hx
    rw [if_neg hrx.ne.symm] at hh
    omega
  obtain ⟨z,j,hj,hxj⟩ := hxN
  have hji := (Finset.mem_erase.mp hj).1
  exact maximum_two_tail_triangle_no_outside_intersection T r L hs hm hcycle htail j hji.symm
    (ShortLollipop.cubic_quota_one_others_avoid T r L hs hd hq1 j hji)
    ⟨x,hxC,Walk.mem_support_of_adj_toSubgraph hxj⟩

end Erdos583TriangleTailTwoDevelopment
