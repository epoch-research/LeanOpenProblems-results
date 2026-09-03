import Submission.ButterflySmoothingReduction

/-! The mixed shortcut reduction: one existing external edge and one fresh smoothing edge. -/
namespace Erdos583ExistingShortcutTriangleDevelopment
open SimpleGraph Erdos583Work
open Erdos583CorePathPiecesDevelopment Erdos583ButterflyRoutesDevelopment
open Erdos583ButterflyPairsDevelopment Erdos583SmoothReachabilityDevelopment
open Erdos583ButterflySmoothingReductionDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma puncture_shortcut_eq_delete_triangle {V : Type*} {G : SimpleGraph V} {x a b : V}
    (hNx : ∀ z, G.Adj x z → z=a ∨ z=b) :
    puncture (G.deleteEdges {s(a,b)}) ({x} : Set V)=
      G.deleteEdges ({s(x,a),s(x,b),s(a,b)} : Set (Sym2 V)) := by
  ext u v
  constructor
  · rintro ⟨he,hu,hv⟩
    obtain ⟨huv,hnab⟩ := deleteEdges_adj.mp he
    refine deleteEdges_adj.mpr ⟨huv,?_⟩
    rintro (he|he|he)
    · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hu rfl
      · exact hv rfl
    · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hu rfl
      · exact hv rfl
    · exact hnab he
  · intro he
    obtain ⟨huv,hn⟩ := deleteEdges_adj.mp he
    refine ⟨deleteEdges_adj.mpr ⟨huv,fun hh ↦ hn (Or.inr (Or.inr hh))⟩,?_,?_⟩
    · intro hu
      have hux : u=x := hu
      subst u
      rcases hNx v huv with rfl | rfl
      · exact hn (Or.inl rfl)
      · exact hn (Or.inr (Or.inl rfl))
    · intro hv
      have hvx : v=x := hv
      subst v
      rcases hNx u huv.symm with rfl | rfl
      · exact hn (Or.inl Sym2.eq_swap)
      · exact hn (Or.inr (Or.inl Sym2.eq_swap))

lemma failure_no_one_existing_one_fresh_shortcut {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {F₀ G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hFG : F₀ ≤ G) (hF : SupportConnected F₀) {r x y a b c d : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hdis : Disjoint ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 (Fin n))) F₀.edgeSet)
    (hcover : G.edgeSet=F₀.edgeSet ∪ {s(r,x),s(x,y),s(r,y)})
    (hrF : r ∈ F₀.support)
    (hxa : F₀.Adj x a) (hxb : F₀.Adj x b) (hab : F₀.Adj a b)
    (har : a ≠ r) (hbr : b ≠ r) (hay : a ≠ y) (hby : b ≠ y)
    (hNx : ∀ z, F₀.Adj x z → z=a ∨ z=b)
    (hyc : F₀.Adj y c) (hyd : F₀.Adj y d) (hcd : c ≠ d)
    (hNy : ∀ z, F₀.Adj y z → z=c ∨ z=d) (hncd : ¬F₀.Adj c d) : False := by
  classical
  let F := puncture (F₀.deleteEdges {s(a,b)}) ({x} : Set (Fin n))
  have hFF : F ≤ F₀ := (puncture_le _ _).trans (deleteEdges_le _)
  have hFe : F=F₀.deleteEdges ({s(x,a),s(x,b),s(a,b)} : Set (Sym2 (Fin n))) :=
    puncture_shortcut_eq_delete_triangle hNx
  have hFs : F.edgeSet=F₀.edgeSet \ {s(x,a),s(x,b),s(a,b)} := by
    rw [hFe,edgeSet_deleteEdges]
  let f : Fin 5 → Fin n := ![x,r,y,a,b]
  have hf : Function.Injective f := by
    apply List.nodup_ofFn.mp
    simp [f,List.ofFn_succ,hrx.ne.symm,hxy.ne,hxa.ne,hxb.ne,hry.ne,
      har.symm,hbr.symm,hay.symm,hby.symm,hab.ne]
  have hfa : ∀ i, G.Adj (f (baseSource i)) (f (baseTarget i)) := by
    intro i
    fin_cases i
    · exact hrx.symm
    · exact hry
    · exact hxy.symm
    · exact hFG hxa
    · exact hFG hab
    · exact (hFG hxb).symm
  have hcore : coreEdges baseSource baseTarget f=
      ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 (Fin n))) ∪ {s(x,a),s(x,b),s(a,b)} := by
    rw [base_coreEdges_eq]
    ext e
    simp [f,Sym2.eq_swap,or_comm,or_left_comm,or_assoc]
  have hFD : Disjoint (coreEdges baseSource baseTarget f) F.edgeSet := by
    rw [hcore]
    apply Set.disjoint_left.mpr
    rintro e (he|he) hh
    · exact Set.disjoint_left.mp hdis he (edgeSet_mono hFF hh)
    · rw [hFs] at hh
      exact hh.2 he
  have hext : ({s(x,a),s(x,b),s(a,b)} : Set (Sym2 (Fin n))) ⊆ F₀.edgeSet := by
    rintro e (rfl|rfl|rfl)
    · exact hxa
    · exact hxb
    · exact hab
  have hFC : G.edgeSet=F.edgeSet ∪ coreEdges baseSource baseTarget f := by
    rw [hcore,hcover,hFs]
    have hh : F₀.edgeSet \ {s(x,a),s(x,b),s(a,b)} ∪ {s(x,a),s(x,b),s(a,b)}=F₀.edgeSet :=
      Set.diff_union_of_subset hext
    rw [←hh]
    ext e
    simp only [Set.mem_union,Set.mem_diff]
    tauto
  have hhub : f 0 ∉ F.support := by
    rintro ⟨v,hv⟩
    exact hv.2.1 rfl
  have hr : f 1 ∈ F.support := by
    obtain ⟨v,hv⟩ := hrF
    refine ⟨v,deleteEdges_adj.mpr ⟨hv,?_⟩,hrx.ne,?_⟩
    · intro he
      rcases Sym2.eq_iff.mp he with ⟨h,_⟩ | ⟨h,_⟩
      · exact har h.symm
      · exact hbr h.symm
    · intro he
      have hvx : v=x := he
      subst v
      rcases hNx r hv.symm with hh | hh
      · exact har hh.symm
      · exact hbr hh.symm
  have hnxy : ¬F₀.Adj x y := fun h ↦ Set.disjoint_left.mp hdis (Or.inr (Or.inl rfl)) h
  have hycF : F.Adj (f 2) c := by
    refine ⟨deleteEdges_adj.mpr ⟨hyc,?_⟩,hxy.ne.symm,?_⟩
    · intro he
      rcases Sym2.eq_iff.mp he with ⟨h,_⟩ | ⟨h,_⟩
      · exact hay h.symm
      · exact hby h.symm
    · intro he
      have hcx : c=x := he
      exact hnxy (hcx ▸ hyc.symm)
  have hydF : F.Adj (f 2) d := by
    refine ⟨deleteEdges_adj.mpr ⟨hyd,?_⟩,hxy.ne.symm,?_⟩
    · intro he
      rcases Sym2.eq_iff.mp he with ⟨h,_⟩ | ⟨h,_⟩
      · exact hay h.symm
      · exact hby h.symm
    · intro he
      have hdx : d=x := he
      exact hnxy (hdx ▸ hyd.symm)
  apply failure_no_smooth_butterfly hsmall hG hfail (hFF.trans hFG) f hf hfa hFD hFC hhub hr
    hycF hydF hcd (fun z hz ↦ hNy z (hFF hz)) (fun h ↦ hncd (hFF h))
  exact puncture_shortcut_two_reachable hF hxa hNx

end Erdos583ExistingShortcutTriangleDevelopment
