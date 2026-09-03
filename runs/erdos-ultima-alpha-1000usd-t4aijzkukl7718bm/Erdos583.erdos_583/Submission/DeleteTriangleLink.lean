import Submission.DegreeTwoFourTriangle

/-! Deleting a degree-two triangular tip while preserving the remaining support connectivity. -/
namespace Erdos583DeleteTriangleLinkDevelopment
open SimpleGraph Erdos583Work
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma puncture_pair_reachable_of_leaf {V : Type*} {G : SimpleGraph V} {x y r u v : V}
    (hconn : (G.induce ({x}ᶜ : Set V)).Connected)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x)
    (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) (hvy : v ≠ y) :
    (puncture G ({x,y} : Set V)).Reachable u v := by
  classical
  let f (z : ({x}ᶜ : Set V)) := if z.val=y then r else z.val
  have hedge (s t : ({x}ᶜ : Set V)) (hst : (G.induce ({x}ᶜ : Set V)).Adj s t) :
      (puncture G ({x,y} : Set V)).Reachable (f s) (f t) := by
    by_cases hs : s.val=y
    · have ht : t.val ≠ y := fun he ↦ hst.ne (Subtype.ext (hs.trans he.symm))
      simp only [f,if_pos hs,if_neg ht]
      rcases hNy t.val (hs ▸ hst) with he | he
      · rw [he]
      · exact (t.property he).elim
    by_cases ht : t.val=y
    · simp only [f,if_neg hs,if_pos ht]
      rcases hNy s.val (ht ▸ hst.symm) with he | he
      · rw [he]
      · exact (s.property he).elim
    simp only [f,if_neg hs,if_neg ht]
    exact (show (puncture G ({x,y} : Set V)).Adj s.val t.val from
      ⟨hst,by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using And.intro s.property hs,
        by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using And.intro t.property ht⟩).reachable
  have hh := reachable_map_to_reachable f hedge (hconn.preconnected ⟨u,hux⟩ ⟨v,hvx⟩)
  simpa only [f,if_neg huy,if_neg hvy] using hh

lemma puncture_pair_le_delete_triangle {V : Type*} (G : SimpleGraph V) (r x y : V) :
    puncture G ({x,y} : Set V) ≤ G.deleteEdges ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V)) := by
  intro u v huv
  refine deleteEdges_adj.mpr ⟨huv.1,?_⟩
  rintro (he|he|he)
  · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact huv.2.2 (Or.inl rfl)
    · exact huv.2.1 (Or.inl rfl)
  · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact huv.2.1 (Or.inl rfl)
    · exact huv.2.2 (Or.inl rfl)
  · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact huv.2.2 (Or.inr rfl)
    · exact huv.2.1 (Or.inr rfl)

lemma delete_triangle_tip_support {V : Type*} {G : SimpleGraph V} {r x y : V}
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x) :
    y ∉ (G.deleteEdges ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V))).support := by
  rintro ⟨v,hv⟩
  obtain ⟨hv,hn⟩ := deleteEdges_adj.mp hv
  rcases hNy v hv with rfl | rfl
  · exact hn (Or.inr (Or.inr Sym2.eq_swap))
  · exact hn (Or.inr (Or.inl Sym2.eq_swap))

lemma delete_triangle_connected_of_tip_link {V : Type*} {G : SimpleGraph V}
    (hG : G.Connected) {r x y : V} (hNy : ∀ z, G.Adj y z → z=r ∨ z=x)
    (hlink : (G.deleteEdges ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V))).Reachable r x) :
    SupportConnected (G.deleteEdges ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V))) := by
  classical
  let F := G.deleteEdges ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V))
  let f (z : V) := if z=y then r else z
  have hedge (u v : V) (huv : G.Adj u v) : F.Reachable (f u) (f v) := by
    by_cases hu : u=y
    · subst u
      have hv : v ≠ y := huv.ne.symm
      simp only [f,if_pos rfl,if_neg hv]
      rcases hNy v huv with rfl | rfl
      · exact .rfl
      · exact hlink
    by_cases hv : v=y
    · subst v
      simp only [f,if_neg hu,if_pos rfl]
      rcases hNy u huv.symm with rfl | rfl
      · exact .rfl
      · exact hlink.symm
    simp only [f,if_neg hu,if_neg hv]
    by_cases he : s(u,v) ∈ ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 V))
    · rcases he with he | he | he
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hlink
        · exact hlink.symm
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact (hv rfl).elim
        · exact (hu rfl).elim
      · rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact (hv rfl).elim
        · exact (hu rfl).elim
    · exact (show F.Adj u v from deleteEdges_adj.mpr ⟨huv,he⟩).reachable
  have hy : y ∉ F.support := delete_triangle_tip_support hNy
  intro u hu v hv
  have huy : u ≠ y := fun he ↦ hy (he ▸ hu)
  have hvy : v ≠ y := fun he ↦ hy (he ▸ hv)
  simpa only [f,if_neg huy,if_neg hvy] using reachable_map_to_reachable f hedge (hG.preconnected u v)

end Erdos583DeleteTriangleLinkDevelopment
