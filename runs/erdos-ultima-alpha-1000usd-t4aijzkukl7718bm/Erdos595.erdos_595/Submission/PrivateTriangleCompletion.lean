import Submission.PrivateTriangleBase
import Submission.PrivateTriangleCertificate
import Submission.SecondArcNormalForm

/-!
Adjoining a private triangle at each vertex that lies in no triangle.
The second-right four-clique obstruction cannot enter the new vertices.
This is a normalization result, not a solution of Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595PrivateTriangleCompletion
open Erdos595ArcAdjoint

variable {V : Type*} (H : SimpleGraph V)

private noncomputable def state (u : Center H) : Vertex H → Fin 5 := by
  classical
  exact fun v => match v with
    | .inl a => if a = u.val then 0 else if H.Adj u.val a then 3 else 4
    | .inr a => if a.1 = u then if a.2 then 2 else 1 else 4

private lemma allowed_symm {a b : Fin 5} :
    Erdos595PrivateTriangleCertificate.Allowed a b →
      Erdos595PrivateTriangleCertificate.Allowed b a := by
  fin_cases a <;> fin_cases b <;> decide +kernel

private lemma state_adj (u : Center H) {a b : Vertex H} (hab : (graph H).Adj a b) :
    Erdos595PrivateTriangleCertificate.Allowed (state H u a) (state H u b) := by
  classical
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change H.Adj a b at hab
      by_cases ha : a = u.val
      · subst a
        have hb := hab.ne.symm
        simp [state,hb,hab,Erdos595PrivateTriangleCertificate.Allowed]
      · by_cases hb : b = u.val
        · subst b
          have hh := hab.symm
          simp [state,ha,hh,Erdos595PrivateTriangleCertificate.Allowed]
        · by_cases hua : H.Adj u.val a <;> by_cases hub : H.Adj u.val b
          · exact (u.property a b hua hub hab).elim
          all_goals simp [state,ha,hb,hua,hub,Erdos595PrivateTriangleCertificate.Allowed]
    | inr b =>
      change a = b.1.val at hab
      subst a
      by_cases hb : b.1 = u
      · rcases b with ⟨w,t⟩
        change w = u at hb
        subst w
        cases t <;> simp [state,Erdos595PrivateTriangleCertificate.Allowed]
      · have hb' : b.1.val ≠ u.val := fun he => hb (Subtype.ext he)
        by_cases hu : H.Adj u.val b.1.val <;>
          simp [state,hb,hb',hu,Erdos595PrivateTriangleCertificate.Allowed]
  | inr a =>
    cases b with
    | inl b =>
      apply allowed_symm
      change a.1.val = b at hab
      subst b
      by_cases ha : a.1 = u
      · rcases a with ⟨w,t⟩
        change w = u at ha
        subst w
        cases t <;> simp [state,Erdos595PrivateTriangleCertificate.Allowed]
      · have ha' : a.1.val ≠ u.val := fun he => ha (Subtype.ext he)
        by_cases hu : H.Adj u.val a.1.val <;>
          simp [state,ha,ha',hu,Erdos595PrivateTriangleCertificate.Allowed]
    | inr b =>
      rcases a with ⟨w,s⟩
      rcases b with ⟨z,t⟩
      change w = z ∧ s ≠ t at hab
      rcases hab with ⟨he,hn⟩
      subst z
      by_cases hz : w = u
      · subst w
        cases s <;> cases t <;> simp_all [state,Erdos595PrivateTriangleCertificate.Allowed]
      · simp [state,hz,Erdos595PrivateTriangleCertificate.Allowed]

/-- The finite obstruction cannot use ANY of the new private vertices. -/
theorem no_new_image (f : Erdos595PrivateTriangleCertificate.A2 →g graph H)
    (p : Arc Erdos595PrivateTriangleCertificate.A1) (u : Center H) (b : Bool) :
    f p ≠ Sum.inr (u,b) := by
  intro he
  have hh := Erdos595PrivateTriangleCertificate.no_private_arc
    (fun q => state H u (f q)) (fun a b hab => state_adj H u (f.map_adj hab)) p
  rw [he] at hh
  cases b <;> simp [state] at hh

/-- Every map of the second arc four-clique factors through the old graph. -/
noncomputable def factor (f : Erdos595PrivateTriangleCertificate.A2 →g graph H) :
    Erdos595PrivateTriangleCertificate.A2 →g H := by
  classical
  have hex : ∀ p, ∃ v : V, f p = Sum.inl v := by
    intro p
    cases he : f p with
    | inl v => exact ⟨v,rfl⟩
    | inr w => exact (no_new_image H f p w.1 w.2 he).elim
  choose g hg using hex
  refine ⟨g,?_⟩
  intro p q hpq
  have he := f.map_adj hpq
  rw [hg p,hg q] at he
  exact he

private noncomputable def rightHom {W : Type*} {G : SimpleGraph W}
    (f : H →g G) : right H →g right G :=
  toRight (f.comp (fromRight SimpleGraph.Hom.id))

private lemma cliqueFree_of_hom {X Y : Type*} {F : SimpleGraph X} {G : SimpleGraph Y}
    {n : ℕ} (f : F →g G) (hG : G.CliqueFree n) : F.CliqueFree n := by
  classical
  by_contra hn
  let g := f.comp (SimpleGraph.topEmbeddingOfNotCliqueFree hn).toHom
  let e : (⊤ : SimpleGraph (Fin n)) ↪g G :=
    { toFun := g
      inj' := g.injective_of_top_hom
      map_rel_iff' := by
        intro a b
        exact ⟨fun h he => h.ne (congrArg g he), fun h => g.map_adj h⟩ }
  exact SimpleGraph.not_cliqueFree_of_top_embedding e hG

/-- Private completion preserves the FULL second-right four-clique bound. -/
theorem second_right_cliqueFree_iff :
    (right (right (graph H))).CliqueFree 4 ↔ (right (right H)).CliqueFree 4 := by
  constructor
  · intro hc
    let f := rightHom (right H) (rightHom H (oldEmbedding H).toHom)
    exact cliqueFree_of_hom f hc
  · intro hc
    classical
    by_contra hn
    let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
    let f := factor H (fromRight (fromRight e.toHom))
    have hf := toRight (toRight f)
    exact SimpleGraph.not_cliqueFree_of_top_embedding (SimpleGraph.Embedding.refl :
      Erdos595PrivateTriangleCertificate.K4 ↪g Erdos595PrivateTriangleCertificate.K4)
      (cliqueFree_of_hom hf hc)

/-- Every vertex of the completed graph lies in a triangle. -/
theorem every_vertex_triangle (v : Vertex H) :
    ∃ a b, (graph H).Adj v a ∧ (graph H).Adj v b ∧ (graph H).Adj a b := by
  classical
  cases v with
  | inl v =>
    by_cases hv : Bare H v
    · let u : Center H := ⟨v,hv⟩
      exact ⟨.inr (u,false),.inr (u,true),rfl,rfl,rfl,by simp⟩
    · simp only [Bare,not_forall,not_not] at hv
      obtain ⟨a,b,ha,hb,hab⟩ := hv
      exact ⟨.inl a,.inl b,ha,hb,hab⟩
  | inr w =>
    rcases w with ⟨u,t⟩
    refine ⟨.inl u.val,.inr (u,!t),rfl,⟨rfl,?_⟩,rfl⟩
    cases t <;> simp

private lemma private_adj_iff (u : Center H) (t : Bool) (v : Vertex H) :
    (graph H).Adj (.inr (u,t)) v ↔ v = .inl u.val ∨ v = .inr (u,!t) := by
  cases v with
  | inl v => simp [graph,eq_comm]
  | inr w =>
    rcases w with ⟨z,s⟩
    cases t <;> cases s <;> simp [graph,eq_comm]

private lemma old_triangle_cases {a : V} {b c : Vertex H}
    (hab : (graph H).Adj (.inl a) b) (hac : (graph H).Adj (.inl a) c)
    (hbc : (graph H).Adj b c) :
    (∃ v w, b = .inl v ∧ c = .inl w ∧ H.Adj a v ∧ H.Adj a w ∧ H.Adj v w) ∨
    ∃ u : Center H, a = u.val ∧
      ((b = .inr (u,false) ∧ c = .inr (u,true)) ∨
       (b = .inr (u,true) ∧ c = .inr (u,false))) := by
  cases b with
  | inl b =>
    cases c with
    | inl c => exact Or.inl ⟨b,c,rfl,rfl,hab,hac,hbc⟩
    | inr c =>
      change H.Adj a b at hab
      change a = c.1.val at hac
      change b = c.1.val at hbc
      exact (hab.ne (hac.trans hbc.symm)).elim
  | inr b =>
    cases c with
    | inl c =>
      change a = b.1.val at hab
      change H.Adj a c at hac
      change b.1.val = c at hbc
      exact (hac.ne (hab.trans hbc)).elim
    | inr c =>
      rcases b with ⟨u,t⟩
      rcases c with ⟨z,s⟩
      change a = u.val at hab
      change u = z ∧ t ≠ s at hbc
      rcases hbc with ⟨he,hne⟩
      subst z
      refine Or.inr ⟨u,hab,?_⟩
      cases t <;> cases s <;> simp_all

/-- Completion preserves the fact that triangles are vertex-disjoint. -/
theorem vertex_disjoint
    (hH : Erdos595SecondArcTriangleStructure.VertexDisjointTriangles H) :
    Erdos595SecondArcTriangleStructure.VertexDisjointTriangles (graph H) := by
  intro a b c d e hab hac hbc had hae hde
  cases a with
  | inl a =>
    rcases old_triangle_cases H hab hac hbc with
      ⟨v,w,rfl,rfl,hv,hw,hvw⟩ | ⟨u,ha,hbc⟩
    · rcases old_triangle_cases H had hae hde with
        ⟨x,y,rfl,rfl,hx,hy,hxy⟩ | ⟨u,ha,hde⟩
      · rcases hH hv hw hvw hx hy hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inl ⟨rfl,rfl⟩
        · exact Or.inr ⟨rfl,rfl⟩
      · exact (u.property v w (ha ▸ hv) (ha ▸ hw) hvw).elim
    · rcases old_triangle_cases H had hae hde with
        ⟨x,y,rfl,rfl,hx,hy,hxy⟩ | ⟨z,hz,hde⟩
      · exact (u.property x y (ha ▸ hx) (ha ▸ hy) hxy).elim
      · have huz : u = z := Subtype.ext (ha.symm.trans hz)
        subst z
        rcases hbc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
          rcases hde with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inl ⟨rfl,rfl⟩
        · exact Or.inr ⟨rfl,rfl⟩
        · exact Or.inr ⟨rfl,rfl⟩
        · exact Or.inl ⟨rfl,rfl⟩
  | inr w =>
    rcases w with ⟨u,t⟩
    rw [private_adj_iff] at hab hac had hae
    rcases hab with rfl | rfl <;> rcases hac with rfl | rfl <;>
      rcases had with rfl | rfl <;> rcases hae with rfl | rfl <;>
      first | exact (hbc.ne rfl).elim | exact (hde.ne rfl).elim |
        exact Or.inl ⟨rfl,rfl⟩ | exact Or.inr ⟨rfl,rfl⟩

private def selected (S : Set V) : Set (Vertex H) :=
  {v | match v with
    | .inl a => a ∈ S
    | .inr w => w.2 = false ∧ w.1.val ∉ S}

private lemma selected_hit (S : Set V)
    (hS : ∀ a b c, H.Adj a b → H.Adj a c → H.Adj b c →
      a ∈ S ∨ b ∈ S ∨ c ∈ S)
    (a b c : Vertex H) (hab : (graph H).Adj a b) (hac : (graph H).Adj a c)
    (hbc : (graph H).Adj b c) :
    a ∈ selected H S ∨ b ∈ selected H S ∨ c ∈ selected H S := by
  classical
  cases a with
  | inl a =>
    rcases old_triangle_cases H hab hac hbc with
      ⟨v,w,rfl,rfl,hv,hw,hvw⟩ | ⟨u,ha,hbc⟩
    · exact hS a v w hv hw hvw
    · subst a
      by_cases hu : u.val ∈ S
      · exact Or.inl hu
      · rcases hbc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inr (Or.inl ⟨rfl,hu⟩)
        · exact Or.inr (Or.inr ⟨rfl,hu⟩)
  | inr w =>
    rcases w with ⟨u,t⟩
    rw [private_adj_iff] at hab hac
    rcases hab with rfl | rfl <;> rcases hac with rfl | rfl
    · exact (hbc.ne rfl).elim
    · by_cases hu : u.val ∈ S
      · exact Or.inr (Or.inl hu)
      · cases t <;> simp [selected,hu]
    · by_cases hu : u.val ∈ S
      · exact Or.inr (Or.inr hu)
      · cases t <;> simp [selected,hu]
    · exact (hbc.ne rfl).elim

/-- An independent transversal also survives private completion. -/
theorem independent_transversal
    (hH : Erdos595SecondArcNormalForm.IndependentTriangleTransversal H) :
    Erdos595SecondArcNormalForm.IndependentTriangleTransversal (graph H) := by
  classical
  obtain ⟨S,hS,hind⟩ := hH
  have hit : ∀ a b c, H.Adj a b → H.Adj a c → H.Adj b c →
      a ∈ S ∨ b ∈ S ∨ c ∈ S := by
    intro a b c hab hac hbc
    by_contra hn
    simp only [not_or] at hn
    exact hS _ (SimpleGraph.is3Clique_triple_iff.mpr
      (show (H.induce Sᶜ).Adj ⟨a,hn.1⟩ ⟨b,hn.2.1⟩ ∧
        (H.induce Sᶜ).Adj ⟨a,hn.1⟩ ⟨c,hn.2.2⟩ ∧
        (H.induce Sᶜ).Adj ⟨b,hn.2.1⟩ ⟨c,hn.2.2⟩ from ⟨hab,hac,hbc⟩))
  refine ⟨selected H S,?_,?_⟩
  · intro t ht
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp ht
    rcases selected_hit H S hit a.val b.val c.val hab hac hbc with ha | hb | hc
    · exact a.property ha
    · exact b.property hb
    · exact c.property hc
  · intro a ha b hb hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact hind a ha b hb hab
      | inr b =>
        change a = b.1.val at hab
        exact hb.2 (hab ▸ ha)
    | inr a =>
      cases b with
      | inl b =>
        change a.1.val = b at hab
        exact ha.2 (hab.symm ▸ hb)
      | inr b =>
        exact hab.2 (ha.1.trans hb.1.symm)

/-- The triangle fibers now cover the whole base, as well as being disjoint. -/
def PartitionedTriangleBase {W : Type*} (G : SimpleGraph W) : Prop :=
  Erdos595SecondArcNormalForm.SparseTriangleBase G ∧
    ∀ v, ∃ a b, G.Adj v a ∧ G.Adj v b ∧ G.Adj a b

theorem partitioned (hH : Erdos595SecondArcNormalForm.SparseTriangleBase H) :
    PartitionedTriangleBase (graph H) :=
  ⟨⟨independent_transversal H hH.1,vertex_disjoint H hH.2⟩,every_vertex_triangle H⟩

universe u
open Erdos595Work

/-- An exact sharper witness normal form, still not an existence theorem. -/
theorem witness_partitioned_normal_form :
    (∃ (W : Type u) (G : SimpleGraph W), G.CliqueFree 4 ∧
      ¬IsCountableUnionOfTriangleFree G) ↔
    (∃ (W : Type u) (G : SimpleGraph W), PartitionedTriangleBase G ∧
      (right (right G)).CliqueFree 4 ∧
      ¬IsCountableUnionOfTriangleFree (right (right G))) := by
  constructor
  · rintro ⟨W,G,hG,hn⟩
    let A := arcGraph (arcGraph G)
    have hA := Erdos595SecondArcNormalForm.second_arc_sparse G
    refine ⟨_,graph A,partitioned A hA,?_,?_⟩
    · exact (second_right_cliqueFree_iff A).mpr
        ((Erdos595SecondArcReflection.right_twice_arc_twice_cliqueFree_iff G).mpr hG)
    · intro hc
      let f := rightHom (right A) (rightHom A (oldEmbedding A).toHom)
      exact hn (Erdos595SecondArcReflection.source_cover_of_twice_cover G
        (countable_union_of_hom f hc))
  · rintro ⟨W,G,_,hG,hn⟩
    exact ⟨_,right (right G),hG,hn⟩


/-- The partitioned-base class is sufficient for the universal covering question. -/
theorem universal_cover_partitioned_iff :
    (∀ (W : Type u) (G : SimpleGraph W), G.CliqueFree 4 →
      IsCountableUnionOfTriangleFree G) ↔
    (∀ (W : Type u) (G : SimpleGraph W), PartitionedTriangleBase G →
      (right (right G)).CliqueFree 4 →
      IsCountableUnionOfTriangleFree (right (right G))) := by
  constructor
  · exact fun h W G _ hG => h _ _ hG
  · intro h W G hG
    classical
    by_contra hn
    obtain ⟨A,K,hK,h₄,hnot⟩ := witness_partitioned_normal_form.mp ⟨W,G,hG,hn⟩
    exact hnot (h A K hK h₄)

#print axioms universal_cover_partitioned_iff

#print axioms independent_transversal
#print axioms partitioned
#print axioms witness_partitioned_normal_form

#print axioms every_vertex_triangle
#print axioms vertex_disjoint

#print axioms no_new_image
#print axioms factor
#print axioms second_right_cliqueFree_iff
end Erdos595PrivateTriangleCompletion
