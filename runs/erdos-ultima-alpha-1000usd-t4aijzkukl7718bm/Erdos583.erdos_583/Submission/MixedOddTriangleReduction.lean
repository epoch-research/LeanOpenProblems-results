import Submission.MixedConnectedReduction

/-! The cubic/quartic triangle reduction at an arbitrary odd root. -/
namespace Erdos583MixedOddTriangleReductionDevelopment
open SimpleGraph Erdos583Work
open Erdos583MixedTriangleFreshDevelopment Erdos583MixedConnectedReductionDevelopment
open Erdos583PunctureConnectivityDevelopment Erdos583LeafPunctureDevelopment
open Erdos583CubicTriangleOddAttachmentDevelopment
open scoped Classical
set_option maxHeartbeats 3000000
set_option Elab.async false

lemma mixed_odd_triangle_reduction {n : ℕ} (hsmall : VertexCritical.SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected) {r x y a b c : Fin n}
    (hrx : G.Adj r x) (hxy : G.Adj x y) (hry : G.Adj r y)
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hyc : G.Adj y c)
    (har : a ≠ r) (hbr : b ≠ r) (hay : a ≠ y) (hby : b ≠ y)
    (hab : a ≠ b) (hcr : c ≠ r) (hcx : c ≠ x)
    (hNx : ∀ z, G.Adj x z → z=r ∨ z=y ∨ z=a ∨ z=b)
    (hNy : ∀ z, G.Adj y z → z=r ∨ z=x ∨ z=c)
    (hrodd : Odd (Nat.card (G.neighborSet r)))
    (hF : SupportConnected (G.deleteEdges ({s(r,x),s(x,y),s(r,y)} : Set (Sym2 (Fin n))))) :
    ∃ E : Finset G.Subgraph, GoodDecomposition G E ∧
      E.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊ := by
  classical
  let C : Set (Sym2 (Fin n)) := {s(r,x),s(x,y),s(r,y)}
  let F := G.deleteEdges C
  let K := puncture G ({x,y} : Set (Fin n))
  have hnxa : s(x,a) ∉ C := by simp [C,hrx.ne.symm,hxy.ne,har,hay]
  have hnxb : s(x,b) ∉ C := by simp [C,hrx.ne.symm,hxy.ne,hbr,hby]
  have hnyc : s(y,c) ∉ C := by simp [C,hry.ne.symm,hxy.ne.symm,hcr,hcx]
  have hxaF : F.Adj x a := deleteEdges_adj.mpr ⟨hxa,hnxa⟩
  have hxbF : F.Adj x b := deleteEdges_adj.mpr ⟨hxb,hnxb⟩
  have hycF : F.Adj y c := deleteEdges_adj.mpr ⟨hyc,hnyc⟩
  have hNxF : ∀ z, F.Adj x z → z=a ∨ z=b := by
    intro z hz
    obtain ⟨hz,hnz⟩ := deleteEdges_adj.mp hz
    rcases hNx z hz with rfl | rfl | h | h
    · exact (hnz (Or.inl Sym2.eq_swap)).elim
    · exact (hnz (Or.inr (Or.inl rfl))).elim
    · exact Or.inl h
    · exact Or.inr h
  have hNyF : ∀ z, F.Adj y z → z=c := by
    intro z hz
    obtain ⟨hz,hnz⟩ := deleteEdges_adj.mp hz
    rcases hNy z hz with rfl | rfl | h
    · exact (hnz (Or.inr (Or.inr Sym2.eq_swap))).elim
    · exact (hnz (Or.inr (Or.inl Sym2.eq_swap))).elim
    · exact h
  have hrNF : F.neighborSet r=G.neighborSet r \ {x,y} := by
    ext z
    simp only [F,mem_neighborSet,deleteEdges_adj,Set.mem_diff,Set.mem_insert_iff,Set.mem_singleton_iff,C]
    simp [hrx.ne,hry.ne]
  have hrOddF : Odd (Nat.card (F.neighborSet r)) := odd_after_two_neighbors hrx hry hxy.ne hrNF hrodd
  by_cases habG : G.Adj a b
  · have habF : F.Adj a b := deleteEdges_adj.mpr ⟨habG,by
      simp [C,har,hbr,hay,hby,hxa.ne.symm,hxb.ne.symm]⟩
    have hX : SupportConnected (puncture F ({x} : Set (Fin n))) :=
      puncture_degree_two_connected_of_shortcut hF hxaF hxbF habF hNxF
    have hK : SupportConnected K := by
      have hh := puncture_leaf_connected hX (fun z hz ↦ hNyF z hz.1)
      simpa only [F,C,puncture_pair_eq_of_triangle_deletion] using hh
    have hrNK : K.neighborSet r=G.neighborSet r \ {x,y} := by
      ext z
      simp [K,puncture_adj,hrx.ne,hry.ne]
    have hrOddK := odd_after_two_neighbors hrx hry hxy.ne hrNK hrodd
    have hrpos : 0 < (K.neighborSet r).ncard := by simpa only [Nat.card_coe_set_eq] using hrOddK.pos
    obtain ⟨z,hz⟩ := (Set.ncard_pos (Set.toFinite _)).mp hrpos
    exact mixed_connected_shortcut_reduction hsmall hG hrx hxy hry hxa hxb hyc har hbr hay hby habG hcr hcx
      hNx hNy hK ⟨z,hz⟩
  · have hdis : Disjoint C F.edgeSet := by
      rw [edgeSet_deleteEdges]
      exact Set.disjoint_left.mpr (fun _ he hh ↦ hh.2 he)
    have hcover : G.edgeSet=F.edgeSet ∪ C := by
      rw [edgeSet_deleteEdges]
      apply (Set.diff_union_of_subset _).symm
      rintro e (rfl|rfl|rfl)
      · exact hrx
      · exact hxy
      · exact hry
    exact mixed_triangle_fresh_reduction hsmall (deleteEdges_le C) hF hrx hxy hry hdis hcover
      hxaF hxbF hycF hab hay hby hcr hcx hNxF hNyF (fun h ↦ habG (deleteEdges_le C h)) hrOddF

end Erdos583MixedOddTriangleReductionDevelopment
