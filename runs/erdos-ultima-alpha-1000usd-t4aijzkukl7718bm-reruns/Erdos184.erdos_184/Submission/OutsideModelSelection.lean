import Submission.OutsideTriangleNormalization
import Submission.OutsideQuadrilateralNormalization
import Submission.QuadrilateralSevenRelabel
import Submission.AttachmentModelCompatibility

/-! Selecting an attachment model from the proved outside-graph classifications. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.OutsideModelSelection
open SmallGraphEncoding CountThreeAttachmentData AttachmentModelFacts AttachmentModelCompatibility
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1000000

lemma adjacency_of_encoding {n N d code : ℕ} (G : SimpleGraph V)
    (e : Fin n ≃ V) (hn : n ≤ N)
    (henc : graph N d code = G.map (e.symm.toEmbedding.trans (Fin.castLEEmb hn)))
    (u v : Fin n) : G.Adj (e u) (e v) ↔ starAdj d code u.val v.val = true := by
  have hh := map_adj_apply (G := G) (f := e.symm.toEmbedding.trans (Fin.castLEEmb hn))
    (a := e u) (b := e v)
  simp only [Function.Embedding.trans_apply,Equiv.coe_toEmbedding,
    Fin.castLEEmb_apply,Equiv.symm_apply_apply] at hh
  rw [← henc] at hh
  exact hh.symm

lemma triangle_model {G : SimpleGraph V}
    (hfour : ∀ v ∈ G.support, G.degree v = 4)
    (C : G.Subgraph) (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (hind : C.IsInduced) (htri : C.verts.ncard = 3)
    (hout : EvenCycleCore.NoTwoCycles (HighGirthCritical.avoid G C.verts)) :
    ∃ (i : Fin 12), (model i).girth = 3 ∧
      ∃ e : Fin (model i).outsideOrder ≃ ↥(G.support \ C.verts), ∀ a b,
        G.Adj (e a).val (e b).val ↔
          s(outsideVertex (model i) a.val,outsideVertex (model i) b.val) ∈ (model i).base := by
  obtain ⟨n,d,code,hn,e,hgood,henc⟩ :=
    OutsideTriangleNormalization.triangle_outside_normalized hfour C hc hind htri hout
  have ha := adjacency_of_encoding (G.induce (G.support \ C.verts)) e hn henc
  simp only [TriangleOutsideData.good,decide_eq_true_eq] at hgood
  rcases hgood with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · refine ⟨0,rfl,e,?_⟩; intro a b; exact (ha a b).trans (base_outside 0 a b)
  · refine ⟨3,rfl,e,?_⟩; intro a b; exact (ha a b).trans (base_outside 3 a b)
  · refine ⟨1,rfl,e,?_⟩; intro a b; exact (ha a b).trans (base_outside 1 a b)
  · refine ⟨2,rfl,e,?_⟩; intro a b; exact (ha a b).trans (base_outside 2 a b)
  · refine ⟨4,rfl,e,?_⟩; intro a b; exact (ha a b).trans (base_outside 4 a b)
  · refine ⟨5,rfl,e,?_⟩; intro a b; exact (ha a b).trans (base_outside 5 a b)

lemma quadrilateral_model {G : SimpleGraph V}
    (hfour : ∀ v ∈ G.support, G.degree v = 4)
    (htri : ∀ u v w, G.Adj u v → G.Adj v w → G.Adj w u → False)
    (C : G.Subgraph) (hc : C.coe.Connected ∧ C.coe.IsRegularOfDegree 2)
    (hind : C.IsInduced) (hquad : C.verts.ncard = 4)
    (hout : EvenCycleCore.NoTwoCycles (HighGirthCritical.avoid G C.verts)) :
    ∃ (i : Fin 12), (model i).girth = 4 ∧
      ∃ e : Fin (model i).outsideOrder ≃ ↥(G.support \ C.verts), ∀ a b,
        G.Adj (e a).val (e b).val ↔
          s(outsideVertex (model i) a.val,outsideVertex (model i) b.val) ∈ (model i).base := by
  obtain ⟨n,code,hn,e,hgood,henc⟩ :=
    OutsideQuadrilateralNormalization.quadrilateral_outside_normalized hfour htri C hc hind hquad hout
  have ha := adjacency_of_encoding (G.induce (G.support \ C.verts)) e hn henc
  have hnlo : 4 ≤ n := by
    by_contra! hh
    interval_cases n <;> simp only [QuadrilateralOutsideData.patterns,List.not_mem_nil] at hgood
  interval_cases n
  · have he : code = 6 := by simpa only [QuadrilateralOutsideData.patterns,List.mem_singleton] using hgood
    subst code
    refine ⟨6,rfl,e,?_⟩; intro a b; exact (ha a b).trans (base_outside 6 a b)
  · have he : code = 30 := by simpa only [QuadrilateralOutsideData.patterns,List.mem_singleton] using hgood
    subst code
    refine ⟨7,rfl,e,?_⟩; intro a b; exact (ha a b).trans (base_outside 7 a b)
  · simp only [QuadrilateralOutsideData.patterns,List.mem_cons,List.not_mem_nil,or_false] at hgood
    rcases hgood with rfl | rfl | rfl
    · refine ⟨8,rfl,e,?_⟩; intro a b; exact (ha a b).trans (base_outside 8 a b)
    · refine ⟨9,rfl,e,?_⟩; intro a b; exact (ha a b).trans (base_outside 9 a b)
    · refine ⟨10,rfl,e,?_⟩; intro a b; exact (ha a b).trans (base_outside 10 a b)
  · obtain ⟨p⟩ := QuadrilateralSevenRelabel.exists_iso code hgood
    refine ⟨11,rfl,p.toEquiv.trans e,?_⟩
    intro a b
    have hh := ha (p a) (p b)
    change G.Adj (e (p a)).val (e (p b)).val ↔ (graph 7 2 code).Adj (p a) (p b) at hh
    exact (hh.trans p.map_rel_iff).trans (base_outside 11 a b)

end Erdos184.OutsideModelSelection
