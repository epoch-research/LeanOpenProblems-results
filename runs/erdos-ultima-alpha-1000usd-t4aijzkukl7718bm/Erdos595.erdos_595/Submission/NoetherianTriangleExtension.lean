import Submission.FiniteCommonIndependentExtension
import Submission.FiniteRankUltrafilterFold

/-!
Finite domination forced by independent extension and finite common-neighborhood
 determination. This gives an obstruction to K5-free Noetherian targets of the
countable generic K4-free graph. It does not settle Erdos 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595NoetherianTriangleExtension
open Erdos595Noetherian Erdos595FiniteCommonIndependent Erdos595BadEdge

variable {V W : Type*}

def FiniteDominating (G : SimpleGraph V) : Prop :=
  ∃ s : Finset V, ∀ v, ∃ w ∈ s, G.Adj w v

/-- Here domination uses open neighborhoods, including at the dominating vertices. -/
theorem finite_dominating [Countable V] (G : SimpleGraph V)
    (hfin : FiniteCommonNeighbors G) (hext : FiniteIndependentExtension G) :
    FiniteDominating G := by
  classical
  by_contra hn
  have hchoice (s : Finset V) : ∃ v, ∀ w ∈ s, ¬G.Adj w v := by
    by_contra h
    push_neg at h
    exact hn ⟨s,h⟩
  obtain ⟨v₀,_⟩ := hext ∅ (by simp)
  letI : Nonempty V := ⟨v₀⟩
  obtain ⟨d,hd⟩ := exists_surjective_nat V
  let v : ℕ → V := Nat.strongRec fun n prev =>
    (hchoice (insert (d n) (Finset.univ.image (fun i : Fin n => prev i.val i.isLt)))).choose
  have hv (n : ℕ) : ¬G.Adj (d n) (v n) ∧ ∀ i : Fin n, ¬G.Adj (v i) (v n) := by
    have he : v n = (hchoice (insert (d n) (Finset.univ.image (fun i : Fin n => v i)))).choose := by
      dsimp only [v]
      rw [Nat.strongRec_eq]
    have hh := (hchoice (insert (d n) (Finset.univ.image (fun i : Fin n => v i)))).choose_spec
    rw [← he] at hh
    exact ⟨hh _ (Finset.mem_insert_self _ _),fun i => hh _ (by simp)⟩
  have hi (i j : ℕ) : ¬G.Adj (v i) (v j) := by
    intro hij
    rcases lt_trichotomy i j with h | h | h
    · exact (hv j).2 ⟨i,h⟩ hij
    · exact hij.ne (congrArg v h)
    · exact (hv i).2 ⟨j,h⟩ hij.symm
  obtain ⟨w,hw⟩ := independent_extension G hfin hext (Set.range v) (by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    exact hi i j)
  obtain ⟨n,rfl⟩ := hd w
  exact (hv n).1 (hw (v n) ⟨n,rfl⟩).symm

def FiniteTriangleFreeExtension (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, (G.induce (↑s : Set V)).CliqueFree 3 →
    ∃ w : V, ∀ v ∈ s, G.Adj v w

lemma independent_of_triangle_extension (G : SimpleGraph V)
    (hext : FiniteTriangleFreeExtension G) : FiniteIndependentExtension G := by
  classical
  intro s hs
  apply hext s
  intro t ht
  obtain ⟨a,b,c,hab,_,_,_⟩ := SimpleGraph.is3Clique_iff.mp ht
  exact hs a a.property b b.property hab

/-- In a neighborhood, an independent request together with its center is
triangle-free in the original graph. -/
lemma neighborhood_independent_extension (G : SimpleGraph V)
    (hext : FiniteTriangleFreeExtension G) (v : V) :
    FiniteIndependentExtension (G.induce (G.neighborSet v)) := by
  classical
  intro s hs
  let t := insert v (s.image Subtype.val)
  have hpair {a b : V} (ha : a ∈ t) (hb : b ∈ t) (hab : G.Adj a b) :
      a = v ∨ b = v := by
    by_contra h
    push_neg at h
    obtain ⟨a,ha',rfl⟩ := Finset.mem_image.mp ((Finset.mem_insert.mp ha).resolve_left h.1)
    obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp ((Finset.mem_insert.mp hb).resolve_left h.2)
    exact hs a ha' b hb' hab
  have htf : (G.induce (↑t : Set V)).CliqueFree 3 := by
    intro q hq
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hq
    rcases hpair a.property b.property hab with ha | hb
    · rcases hpair b.property c.property hbc with hb | hc
      · exact hab.ne (Subtype.ext (ha.trans hb.symm))
      · exact hac.ne (Subtype.ext (ha.trans hc.symm))
    · rcases hpair a.property c.property hac with ha | hc
      · exact hab.ne (Subtype.ext (ha.trans hb.symm))
      · exact hbc.ne (Subtype.ext (hb.trans hc.symm))
  obtain ⟨w,hw⟩ := hext t htf
  refine ⟨⟨w,hw v (Finset.mem_insert_self _ _)⟩,?_⟩
  intro a ha
  exact hw a.val (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a,ha,rfl⟩))

/-- Every vertex has two adjacent detectors, from a fixed finite list, both
adjacent to it. No clique bound is used in this structural conclusion. -/
theorem finite_edge_detectors [Countable V] (G : SimpleGraph V)
    (hfin : FiniteCommonNeighbors G) (hext : FiniteTriangleFreeExtension G) :
    ∃ s : Finset (V × V),
      (∀ p ∈ s, G.Adj p.1 p.2) ∧
      ∀ v, ∃ p ∈ s, G.Adj p.1 v ∧ G.Adj p.2 v := by
  classical
  obtain ⟨s,hs⟩ := finite_dominating G hfin (independent_of_triangle_extension G hext)
  have hn (v : V) : FiniteDominating (G.induce (G.neighborSet v)) :=
    finite_dominating _ (finite_common_induce G hfin _) (neighborhood_independent_extension G hext v)
  choose t ht using hn
  refine ⟨s.biUnion (fun a => (t a).image (fun b => (a,b.val))),?_,?_⟩
  · intro p hp
    obtain ⟨a,ha,hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hp
    exact b.property
  · intro v
    obtain ⟨a,ha,hav⟩ := hs v
    obtain ⟨b,hb,hbv⟩ := ht a ⟨v,hav⟩
    exact ⟨(a,b.val),Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_image.mpr ⟨b,hb,rfl⟩⟩,hav,hbv⟩

def FiniteVertexTriangleCover (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ, ∃ c : V → Fin n, ∀ i, (G.induce {v | c v = i}).CliqueFree 3

lemma triangleFree_of_hom (G : SimpleGraph V) (H : SimpleGraph W)
    (f : G →g H) (hH : H.CliqueFree 3) : G.CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
  exact hH _ (SimpleGraph.is3Clique_triple_iff.mpr
    ⟨f.map_adj hab,f.map_adj hac,f.map_adj hbc⟩)

lemma vertex_cover_of_pieces {I : Type*} [Finite I] (G : SimpleGraph V)
    (S : I → Set V) (hS : ∀ i, (G.induce (S i)).CliqueFree 3)
    (hc : ∀ v, ∃ i, v ∈ S i) : FiniteVertexTriangleCover G := by
  classical
  letI := Fintype.ofFinite I
  choose c hc using hc
  let e := Fintype.equivFin I
  refine ⟨Fintype.card I,e ∘ c,fun i => ?_⟩
  let f : G.induce {v | (e ∘ c) v = i} →g G.induce (S (e.symm i)) :=
    ⟨fun v => ⟨v.val,by
      have he : c v.val = e.symm i := e.injective (v.property.trans (e.apply_symm_apply i).symm)
      exact he ▸ hc v.val⟩,fun h => h⟩
  exact triangleFree_of_hom _ _ f (hS _)

/-- The stronger vertex version of the K4-free conclusion. -/
theorem k4_vertex_cover [Countable V] (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (hfin : FiniteCommonNeighbors G) (hext : FiniteIndependentExtension G) :
    FiniteVertexTriangleCover G := by
  classical
  obtain ⟨s,hs⟩ := finite_dominating G hfin hext
  apply vertex_cover_of_pieces G (fun v : s => G.neighborSet v.val)
  · intro v t ht
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp ht
    exact Erdos595Work.no_adj_common_neighbors hG a.property b.property hab c.property hac hbc
  · intro v
    obtain ⟨w,hw,hwv⟩ := hs v
    exact ⟨⟨w,hw⟩,hwv⟩

lemma common_edge_triangleFree (G : SimpleGraph V) (hG : G.CliqueFree 5)
    {a b : V} (hab : G.Adj a b) :
    (G.induce {v | G.Adj a v ∧ G.Adj b v}).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨x,y,z,hxy,hxz,hyz,_⟩ := SimpleGraph.is3Clique_iff.mp ht
  have h3 : G.IsNClique 3 {x.val,y.val,z.val} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy,hxz,hyz⟩
  have h4 : G.IsNClique 4 (insert b {x.val,y.val,z.val}) :=
    h3.insert (by intro v hv; simp only [Finset.mem_insert,Finset.mem_singleton] at hv
                  rcases hv with rfl | rfl | rfl
                  · exact x.property.2
                  · exact y.property.2
                  · exact z.property.2)
  have h5 : G.IsNClique 5 (insert a (insert b {x.val,y.val,z.val})) :=
    h4.insert (by intro v hv; simp only [Finset.mem_insert,Finset.mem_singleton] at hv
                  rcases hv with rfl | rfl | rfl | rfl
                  · exact hab
                  · exact x.property.1
                  · exact y.property.1
                  · exact z.property.1)
  exact hG _ h5

/-- Allowing K4s in the target is not enough: the obstruction extends to K5-free
Noetherian targets once finite triangle-free extension is available. -/
theorem k5_vertex_cover [Countable V] (G : SimpleGraph V) (hG : G.CliqueFree 5)
    (hfin : FiniteCommonNeighbors G) (hext : FiniteTriangleFreeExtension G) :
    FiniteVertexTriangleCover G := by
  classical
  obtain ⟨s,hs,hcov⟩ := finite_edge_detectors G hfin hext
  apply vertex_cover_of_pieces G (fun p : s => {v | G.Adj p.val.1 v ∧ G.Adj p.val.2 v})
  · exact fun p => common_edge_triangleFree G hG (hs p p.property)
  · intro v
    obtain ⟨p,hp,hpv⟩ := hcov v
    exact ⟨⟨p,hp⟩,hpv⟩

lemma finite_edge_cover (G : SimpleGraph V) (h : FiniteVertexTriangleCover G) :
    FiniteCover G := by
  classical
  obtain ⟨n,c,hc⟩ := h
  apply finite_cover_of_coloring G (C := Sym2 (Fin n))
  refine ⟨Sym2.map c,?_⟩
  intro a b d hab had hbd hm
  have h₁ : s(c a,c b) = s(c a,c d) := hm.1
  have h₂ : s(c a,c b) = s(c b,c d) := hm.2
  have hcb : c a = c b := by
    rcases Sym2.eq_iff.mp h₂ with h | h
    · exact h.1
    · rcases Sym2.eq_iff.mp h₁ with h' | h'
      · exact h.1.trans h'.2.symm
      · exact h'.2.symm
  have hcd : c a = c d := by
    rcases Sym2.eq_iff.mp h₁ with h | h
    · exact hcb.trans h.2
    · exact h.1
  exact hc (c a) _ (SimpleGraph.is3Clique_triple_iff.mpr
    (show (G.induce {v | c v = c a}).Adj ⟨a,rfl⟩ ⟨b,hcb.symm⟩ ∧
      (G.induce {v | c v = c a}).Adj ⟨a,rfl⟩ ⟨d,hcd.symm⟩ ∧
      (G.induce {v | c v = c a}).Adj ⟨b,hcb.symm⟩ ⟨d,hcd.symm⟩ from ⟨hab,had,hbd⟩))

lemma triangle_extension_range (G : SimpleGraph V) (H : SimpleGraph W)
    (hext : FiniteTriangleFreeExtension G) (f : G →g H) :
    FiniteTriangleFreeExtension (H.induce (Set.range f)) := by
  classical
  let pre : Set.range f → V := fun v => v.property.choose
  have hpre (v : Set.range f) : f (pre v) = v.val := v.property.choose_spec
  intro s hs
  let t := s.image pre
  let q : G.induce (↑t : Set V) →g (H.induce (Set.range f)).induce (↑s : Set (Set.range f)) := by
    refine ⟨fun v => ⟨⟨f v.val,⟨v.val,rfl⟩⟩,?_⟩,?_⟩
    · obtain ⟨w,hw,he⟩ := Finset.mem_image.mp v.property
      have hh : (⟨f v.val,⟨v.val,rfl⟩⟩ : Set.range f) = w := Subtype.ext (he ▸ hpre w)
      exact hh ▸ hw
    · exact fun h => f.map_adj h
  obtain ⟨w,hw⟩ := hext t (triangleFree_of_hom _ _ q hs)
  refine ⟨⟨f w,⟨w,rfl⟩⟩,fun v hv => ?_⟩
  have ha := f.map_adj (hw (pre v) (Finset.mem_image.mpr ⟨v,hv,rfl⟩))
  simpa only [hpre] using ha

lemma generic_triangle_extension : FiniteTriangleFreeExtension Erdos595CountableExtension.G := by
  classical
  intro s hs
  obtain ⟨w,_,hw,_⟩ := Erdos595CountableExtension.finite_extension s ∅ hs (by simp)
  exact ⟨w,fun v hv => (hw v hv).symm⟩

/-- An exact finite-dimensional target containing K4s still cannot receive the
generic graph if its clique number is at most four. -/
theorem generic_no_noetherian_k5 (H : SimpleGraph W) (hH : H.CliqueFree 5)
    (hfin : FiniteCommonNeighbors H) :
    ¬Nonempty (Erdos595CountableExtension.G →g H) := by
  classical
  rintro ⟨f⟩
  let S := Set.range f
  letI : Countable S := (Set.countable_range f).to_subtype
  have hc := finite_edge_cover (H.induce S) (k5_vertex_cover (H.induce S)
    (hH.comap (SimpleGraph.Embedding.induce S)) (finite_common_induce H hfin S)
    (triangle_extension_range _ _ generic_triangle_extension f))
  obtain ⟨n,hn⟩ := Erdos595NoCountableK4Target.finiteCover_coloring hc
  let f' : Erdos595CountableExtension.G →g H.induce S :=
    ⟨fun v => ⟨f v,⟨v,rfl⟩⟩,fun h => f.map_adj h⟩
  exact Erdos595NoCountableK4Target.generic_no_finiteCover
    (finite_cover_of_coloring _ (hn.comap f'))

theorem generic_no_finite_rank_k5 {K E : Type*} [Field K] [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] (H : SimpleGraph W) (hH : H.CliqueFree 5)
    (B : LinearMap.BilinForm K E) (r : W → E)
    (hr : ∀ a b, H.Adj a b ↔ B (r a) (r b) = 0) :
    ¬Nonempty (Erdos595CountableExtension.G →g H) :=
  generic_no_noetherian_k5 H hH (Erdos595FiniteRankFold.finite_common H B r hr)

section Bilinear
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- The same finite spanning set determines both directions of orthogonality. -/
lemma finite_common_mutual (H : SimpleGraph W) (B : LinearMap.BilinForm K E)
    (r : W → E) (hr : ∀ a b, H.Adj a b ↔ B (r a) (r b) = 0 ∧ B (r b) (r a) = 0) :
    FiniteCommonNeighbors H := by
  classical
  intro S
  have hfg : (Submodule.span K (r '' S)).FG :=
    (Submodule.fg_iff_finiteDimensional _).mpr inferInstance
  obtain ⟨T,hT,hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (r '' S)).mp hfg
  have hex (x : T) : ∃ a : S, r a.val = x.val := by
    obtain ⟨a,ha,he⟩ := hT x.property
    exact ⟨⟨a,ha⟩,he⟩
  choose f hf using hex
  let t : Finset S := Finset.univ.image f
  refine ⟨t,fun w => ⟨?_,?_⟩⟩
  · intro ht a ha
    have hk : Submodule.span K (T : Set E) ≤
        LinearMap.ker (B.flip (r w)) ⊓ LinearMap.ker (B (r w)) := by
      apply Submodule.span_le.mpr
      intro x hx
      have he : r (f ⟨x,hx⟩).val = x := hf ⟨x,hx⟩
      have hh := (hr _ w).mp (ht (f ⟨x,hx⟩) (Finset.mem_image.mpr
        ⟨⟨x,hx⟩,Finset.mem_univ _,rfl⟩))
      change B x (r w) = 0 ∧ B (r w) x = 0
      simpa only [he] using hh
    apply (hr a w).mpr
    exact hk (hspan ▸ Submodule.subset_span (show r a ∈ r '' S from ⟨a,ha,rfl⟩))
  · intro ht a _
    exact ht a.val a.property

/-- In dimension at most four, even a weak nonisotropic representation of the
generic graph is impossible. No symmetry, exactness, or injectivity is assumed. -/
theorem generic_no_rank_four (B : LinearMap.BilinForm K E)
    (hd : Module.finrank K E ≤ 4)
    (r : Erdos595CountableExtension.Vertex → E)
    (hr : ∀ v, B (r v) (r v) ≠ 0)
    (he : ∀ a b, Erdos595CountableExtension.G.Adj a b → B (r a) (r b) = 0) : False := by
  classical
  let P := {x : E // B x x ≠ 0}
  let H : SimpleGraph P :=
    { Adj x y := B x.val y.val = 0 ∧ B y.val x.val = 0
      symm := fun _ _ h => h.symm
      loopless := fun x h => x.property h.1 }
  have hH : H.CliqueFree 5 := by
    by_contra hn
    let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
    have ho : B.iIsOrtho (fun i : Fin 5 => (e i).val) := by
      intro i j hij
      exact ((e.map_rel_iff).mpr hij).1
    have hi := (LinearMap.BilinForm.linearIndependent_of_iIsOrtho ho
      (fun i => (e i).property)).fintype_card_le_finrank
    simp only [Fintype.card_fin] at hi
    omega
  have hfin : FiniteCommonNeighbors H := finite_common_mutual H B Subtype.val (fun _ _ => Iff.rfl)
  let f : Erdos595CountableExtension.G →g H :=
    ⟨fun v => ⟨r v,hr v⟩,fun h => ⟨he _ _ h,he _ _ h.symm⟩⟩
  exact generic_no_noetherian_k5 H hH hfin ⟨f⟩
end Bilinear

#print axioms finite_dominating
#print axioms finite_edge_detectors
#print axioms k4_vertex_cover
#print axioms k5_vertex_cover
#print axioms generic_no_noetherian_k5
#print axioms generic_no_finite_rank_k5
#print axioms generic_no_rank_four
end Erdos595NoetherianTriangleExtension
