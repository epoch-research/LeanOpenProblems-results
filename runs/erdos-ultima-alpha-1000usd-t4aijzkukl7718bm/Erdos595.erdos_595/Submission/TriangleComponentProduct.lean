import Submission.CompleteFilterEdgeCover

/-!
Triangle components and countably complete reduced products. Finite covers
on individual triangle components suffice, with no uniform palette bound.
This is an obstruction to a candidate family, not a settlement of Erdős 595.
-/

open SimpleGraph Set Filter
namespace Erdos595TriangleComponentProduct
open Erdos595Work Erdos595BadEdge Erdos595CompleteFilterProduct

variable {V W : Type*}

abbrev Edge (G : SimpleGraph V) := {e : Sym2 V // e ∈ G.edgeSet}

/-- Two edges of one triangle; the equivalence closure also joins chains
of triangles sharing edges. -/
def Step (G : SimpleGraph V) (e f : Edge G) : Prop :=
  ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c ∧
    e.val = s(a,b) ∧ f.val = s(a,c)

abbrev Component (G : SimpleGraph V) := Quot (Step G)

def component (G : SimpleGraph V) (e : Edge G) : Component G := Quot.mk _ e

noncomputable def tag (G : SimpleGraph V) (e : Sym2 V) : Option (Component G) := by
  classical
  exact if h : e ∈ G.edgeSet then some (component G ⟨e,h⟩) else none

lemma tag_edge (G : SimpleGraph V) (e : Edge G) : tag G e.val = some (component G e) := by
  classical
  simp only [tag,dif_pos e.property]

lemma triangle_tag (G : SimpleGraph V) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    tag G s(a,b) = tag G s(a,c) ∧ tag G s(a,b) = tag G s(b,c) := by
  have h₁ : Step G ⟨s(a,b),hab⟩ ⟨s(a,c),hac⟩ := ⟨a,b,c,hab,hac,hbc,rfl,rfl⟩
  have h₂ : Step G ⟨s(a,b),hab⟩ ⟨s(b,c),hbc⟩ :=
    ⟨b,a,c,hab.symm,hbc,hac,Sym2.eq_swap,rfl⟩
  have he₁ := congrArg some (Quot.sound h₁)
  have he₂ := congrArg some (Quot.sound h₂)
  exact ⟨(tag_edge G ⟨s(a,b),hab⟩).trans
      (he₁.trans (tag_edge G ⟨s(a,c),hac⟩).symm),
    (tag_edge G ⟨s(a,b),hab⟩).trans
      (he₂.trans (tag_edge G ⟨s(b,c),hbc⟩).symm)⟩

/-- A component is viewed as a spanning edge subgraph, so different
components may share graph vertices. -/
noncomputable def piece (G : SimpleGraph V) (q : Component G) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ tag G s(a,b) = some q
  symm := by intro a b h; exact ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2⟩
  loopless := fun _ h => h.1.ne rfl

/-- Countable palettes can be reused on arbitrarily many triangle components:
a triangle never has edges in different components. -/
theorem cover_of_pieces (G : SimpleGraph V)
    (h : ∀ q, IsCountableUnionOfTriangleFree (piece G q)) :
    IsCountableUnionOfTriangleFree G := by
  classical
  choose c hc using fun q => (countable_union_iff_edge_coloring (piece G q)).mp (h q)
  let color : Sym2 V → ℕ := fun e => match tag G e with
    | none => 0
    | some q => c q e
  apply (countable_union_iff_edge_coloring G).mpr
  refine ⟨color,?_⟩
  intro a b d hab had hbd hm
  let q := component G ⟨s(a,b),hab⟩
  have habq : tag G s(a,b) = some q := tag_edge G ⟨s(a,b),hab⟩
  have hh := triangle_tag G hab had hbd
  have hadq : tag G s(a,d) = some q := hh.1.symm.trans habq
  have hbdq : tag G s(b,d) = some q := hh.2.symm.trans habq
  exact hc q a b d ⟨hab,habq⟩ ⟨had,hadq⟩ ⟨hbd,hbdq⟩
    (by simpa only [color,habq,hadq,hbdq] using hm)

/-- Pulling back a finite cover along a graph homomorphism. -/
lemma finiteCover_comap {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (h : FiniteCover H) : FiniteCover G := by
  classical
  obtain ⟨n,K,hK,hcov⟩ := h
  refine ⟨n,fun j => (K j).comap f,?_,?_⟩
  · intro j s hs
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
    exact hK j _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)
  · intro a b hab
    exact hcov (f a) (f b) (f.map_adj hab)

lemma finiteCover_bot (V : Type*) : FiniteCover (⊥ : SimpleGraph V) :=
  ⟨1,fun _ => ⊥,fun _ => SimpleGraph.cliqueFree_bot (by decide),fun _ _ h => h.elim⟩

variable {I : Type*} {A : I → Type*}
    (F : Filter I) [F.NeBot] (G : ∀ i, SimpleGraph (A i))

abbrev P := graph F G

def evaluation (i : I) : (∀ i, A i) → A i := fun x => x i

/-- The coordinate edge tag may be absent at exceptional coordinates. -/
noncomputable def coordinateTag (e : Edge (P F G)) (i : I) : Option (Component (G i)) :=
  tag (G i) (e.val.map (evaluation i))

lemma step_eventually {e f : Edge (P F G)} (h : Step (P F G) e f) :
    ∀ᶠ i in F, coordinateTag F G e i = coordinateTag F G f i := by
  obtain ⟨a,b,c,hab,hac,hbc,he,hf⟩ := h
  change ∀ᶠ i in F, (G i).Adj (a i) (b i) at hab
  change ∀ᶠ i in F, (G i).Adj (a i) (c i) at hac
  change ∀ᶠ i in F, (G i).Adj (b i) (c i) at hbc
  apply (hab.and (hac.and hbc)).mono
  intro i hi
  simpa only [coordinateTag,he,hf,Sym2.map_mk,evaluation] using
    (triangle_tag (G i) hi.1 hi.2.1 hi.2.2).1

lemma component_eventually {e f : Edge (P F G)}
    (h : component (P F G) e = component (P F G) f) :
    ∀ᶠ i in F, coordinateTag F G e i = coordinateTag F G f i := by
  have ht : Relation.EqvGen (Step (P F G)) e f := Quot.eq.mp h
  clear h
  induction ht with
  | rel e f h => exact step_eventually F G h
  | refl e => exact Filter.Eventually.of_forall fun _ => rfl
  | symm e f h ih => exact ih.mono fun _ h => h.symm
  | trans e f g h₁ h₂ ih₁ ih₂ => exact (ih₁.and ih₂).mono fun _ h => h.1.trans h.2

/-- A fixed product edge picks one triangle component at each coordinate.
If the edge is absent there, use the empty graph instead. -/
noncomputable def anchorGraph (e : Edge (P F G)) (i : I) : SimpleGraph (A i) :=
  match coordinateTag F G e i with
  | none => ⊥
  | some q => piece (G i) q

noncomputable def anchorHom (e : Edge (P F G)) :
    piece (P F G) (component (P F G) e) →g graph F (anchorGraph F G e) where
  toFun := id
  map_rel' := by
    intro a b hab
    let f : Edge (P F G) := ⟨s(a,b),hab.1⟩
    have he : component (P F G) f = component (P F G) e := by
      apply Option.some.inj
      exact (tag_edge (P F G) f).symm.trans hab.2
    have hh := component_eventually F G he
    have hadj : ∀ᶠ i in F, (G i).Adj (a i) (b i) := hab.1
    apply (hadj.and hh).mono
    intro i hi
    have ht : coordinateTag F G f i =
        some (component (G i) ⟨s(a i,b i),hi.1⟩) := tag_edge (G i) ⟨_,hi.1⟩
    have ht' : coordinateTag F G e i =
        some (component (G i) ⟨s(a i,b i),hi.1⟩) := hi.2.symm.trans ht
    change (anchorGraph F G e i).Adj (a i) (b i)
    rw [anchorGraph,ht']
    exact ⟨hi.1,tag_edge (G i) ⟨_,hi.1⟩⟩

/-- Finite coordinate palette bounds may vary with both i and the component.
Countable completeness is used ONLY in the finite-product-cover theorem. -/
theorem pieces_finite [CountableInterFilter F]
    (hG : ∀ i q, FiniteCover (piece (G i) q)) :
    ∀ q, FiniteCover (piece (P F G) q) := by
  intro q
  obtain ⟨e,rfl⟩ := Quot.exists_rep q
  apply finiteCover_comap (anchorHom F G e)
  apply Erdos595CompleteFilterEdgeCover.finite_cover F
  intro i
  unfold anchorGraph
  split
  · exact finiteCover_bot _
  · exact hG i _

/-- In particular, disjoint unions or vertex-gluings of finite Folkman
pieces cannot provide a witness through a countably complete reduced product,
provided their TRIANGLE components still have finite edge covers. -/
theorem countable_cover [CountableInterFilter F]
    (hG : ∀ i q, FiniteCover (piece (G i) q)) :
    IsCountableUnionOfTriangleFree (P F G) :=
  cover_of_pieces _ (fun q => (pieces_finite F G hG q).countable)

/-- Countable graph homomorphisms into a countably complete product reflect
into a single coordinate. This does not claim reflection of induced embeddings. -/
theorem countable_hom_reflection [CountableInterFilter F]
    {W : Type*} [Countable W] (H : SimpleGraph W) (f : H →g P F G) :
    ∃ i, Nonempty (H →g G i) := by
  have he : ∀ a b, ∀ᶠ i in F, H.Adj a b → (G i).Adj (f a i) (f b i) := by
    intro a b
    by_cases h : H.Adj a b
    · exact (f.map_adj h).mono fun _ hi _ => hi
    · exact Filter.Eventually.of_forall fun _ ha => (h ha).elim
  have hh : ∀ᶠ i in F, ∀ a b, H.Adj a b → (G i).Adj (f a i) (f b i) :=
    eventually_countable_forall.mpr fun a => eventually_countable_forall.mpr (he a)
  obtain ⟨i,hi⟩ := hh.exists
  exact ⟨i,⟨⟨fun a => f a i,fun h => hi _ _ h⟩⟩⟩

#print axioms cover_of_pieces
#print axioms pieces_finite
#print axioms countable_cover
#print axioms countable_hom_reflection
end Erdos595TriangleComponentProduct
