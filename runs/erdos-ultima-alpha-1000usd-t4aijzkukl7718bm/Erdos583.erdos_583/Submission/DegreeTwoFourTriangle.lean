import Submission.ButterflySupportBudget

/-! Reducing a triangle with one degree-two vertex and one degree-four vertex. -/
namespace Erdos583DegreeTwoFourTriangleDevelopment
open SimpleGraph Erdos583Work
open Erdos583CorePathPiecesDevelopment Erdos583ButterflyRoutesDevelopment
open Erdos583ButterflyPairsDevelopment Erdos583SmoothReachabilityDevelopment
open Erdos583ExistingShortcutTriangleDevelopment Erdos583ButterflySupportBudgetDevelopment
open Erdos583SupportSmoothingDevelopment Erdos583RestoreTriangleDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma failure_no_triangle_two_four_data {n : ℕ}
    (hsmall : VertexCritical.SmallerOrders n) {F₀ G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊)
    (hFG : F₀ ≤ G) (hF : SupportConnected F₀) {r x y a b : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hdis : Disjoint ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 (Fin n))) F₀.edgeSet)
    (hcover : G.edgeSet=F₀.edgeSet ∪ {s(r,x),s(x,y),s(r,y)})
    (hrF : r ∈ F₀.support) (hyF : y ∉ F₀.support)
    (hxa : F₀.Adj x a) (hxb : F₀.Adj x b) (habne : a ≠ b)
    (har : a ≠ r) (hbr : b ≠ r) (hay : a ≠ y) (hby : b ≠ y)
    (hNx : ∀ z, F₀.Adj x z → z=a ∨ z=b) : False := by
  classical
  by_cases hab : F₀.Adj a b
  ·
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
    have hyF' : f 2 ∉ F.support := fun hh ↦ hyF (support_mono hFF hh)
    have hn02 : f 0 ∉ insert (f 2) F.support := by
      rintro (he|he)
      · exact hxy.ne he
      · exact hhub he
    have hcard : F.support.ncard+2 ≤ n := by
      have hh := (insert (f 0) (insert (f 2) F.support)).ncard_le_card
      rw [Set.ncard_insert_of_notMem hn02,Set.ncard_insert_of_notMem hyF',
        Nat.card_eq_fintype_card,Fintype.card_fin] at hh
      omega
    exact failure_no_butterfly_support_saving hsmall hG hfail (hFF.trans hFG) f hf hfa hFD hFC
      hhub hr hcard (puncture_shortcut_two_reachable hF hxa hNx)
  · let H := smooth F₀ x a b
    have hH : SupportConnected H := smooth_support_connected hF hxa hxb habne hNx
    have hcardF : F₀.support.ncard+1 ≤ n := by
      have hh := (insert y F₀.support).ncard_le_card
      rw [Set.ncard_insert_of_notMem hyF,Nat.card_eq_fintype_card,Fintype.card_fin] at hh
      exact hh
    have hcardH : H.support.ncard+2 ≤ n := by
      have hh : H.support.ncard+1 ≤ F₀.support.ncard := smooth_support_card hxa hxb
      omega
    apply hfail
    apply LowDegreeAdjacency.gallai_of_two_vertex_support_reduction hsmall G H hH hcardH
    intro D hD
    obtain ⟨E,hE,hEc⟩ := smooth_lift hxa hxb habne hNx hab D hD
    obtain ⟨J,hJ,hJc⟩ := restore_triangle_at_support hFG hrx hxy hry hdis hcover
      ⟨x,⟨a,hxa⟩,Or.inr (Or.inl rfl)⟩ E hE
    exact ⟨J,hJ,by omega⟩

end Erdos583DegreeTwoFourTriangleDevelopment
