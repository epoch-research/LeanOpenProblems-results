import Submission.CountableBadEdgeFilter

/-!
The canonical countably complete avoiding edge filter has an exact triangle
coupling: every edge marginal of the triangle filter equals the edge filter.
This does not supply a four-clique coupling or settle Erdős 595.
-/

set_option autoImplicit false
open SimpleGraph Set Filter
namespace Erdos595TriangleFilterCoupling
open Erdos595Work Erdos595CountableBadEdge

variable {V : Type*} (G : SimpleGraph V)

structure Triangle where
  a : V
  b : V
  c : V
  ab : G.Adj a b
  ac : G.Adj a c
  bc : G.Adj b c

abbrev Edge := Erdos595ArcAdjoint.Arc G

def side (i : Fin 3) (t : Triangle G) : Edge G :=
  if i = 0 then ⟨(t.a,t.b),t.ab⟩
  else if i = 1 then ⟨(t.a,t.c),t.ac⟩
  else ⟨(t.b,t.c),t.bc⟩

def avoidTriangle (H : SimpleGraph V) : Set (Triangle G) :=
  {t | ¬H.Adj t.a t.b ∧ ¬H.Adj t.a t.c ∧ ¬H.Adj t.b t.c}

def triangleGenerators : Set (Set (Triangle G)) :=
  {s | ∃ H : SimpleGraph V, H.CliqueFree 3 ∧ s = avoidTriangle G H}

def triangleFilter : Filter (Triangle G) :=
  Filter.countableGenerate (triangleGenerators G)

instance : CountableInterFilter (triangleFilter G) :=
  inferInstanceAs (CountableInterFilter (Filter.countableGenerate _))

lemma avoidTriangle_mem (H : SimpleGraph V) (hH : H.CliqueFree 3) :
    avoidTriangle G H ∈ triangleFilter G :=
  Filter.CountableGenerateSets.basic ⟨H,hH,rfl⟩

lemma side_avoids (H : SimpleGraph V) (i : Fin 3) (t : Triangle G)
    (ht : t ∈ avoidTriangle G H) :
    ¬H.Adj (side G i t).val.1 (side G i t).val.2 := by
  fin_cases i
  · exact ht.1
  · exact ht.2.1
  · exact ht.2.2

lemma map_side_le (i : Fin 3) :
    Filter.map (side G i) (triangleFilter G) ≤ coveringFilter G := by
  apply Filter.le_countableGenerate_iff_of_countableInterFilter.mpr
  rintro s ⟨H,hH,rfl⟩
  change {t | ¬H.Adj (side G i t).val.1 (side G i t).val.2} ∈ triangleFilter G
  exact Filter.mem_of_superset (avoidTriangle_mem G H hH) (side_avoids G H i)

/-- If every sufficiently unrestricted triangle has its designated side in S,
then this is true of any designated oriented edge in such a triangle. -/
lemma side_of_triangle {I : Type*} (H : I → SimpleGraph V) (i : Fin 3)
    (S : Set (Edge G))
    (hS : ∀ t : Triangle G, (∀ j, t ∈ avoidTriangle G (H j)) → side G i t ∈ S)
    (a b c : V) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (ha : ∀ j, ¬(H j).Adj a b) (hb : ∀ j, ¬(H j).Adj a c)
    (hc : ∀ j, ¬(H j).Adj b c) : (⟨(a,b),hab⟩ : Edge G) ∈ S := by
  fin_cases i
  · exact hS ⟨a,b,c,hab,hac,hbc⟩ (fun j => ⟨ha j,hb j,hc j⟩)
  · exact hS ⟨a,c,b,hac,hab,hbc.symm⟩
      (fun j => ⟨hb j,ha j,fun h => hc j h.symm⟩)
  · exact hS ⟨c,a,b,hac.symm,hbc.symm,hab⟩
      (fun j => ⟨fun h => hb j h.symm,fun h => hc j h.symm,ha j⟩)

/-- Membership in an edge marginal does not merely extend the original
filter: it is already membership in the original filter. -/
lemma le_map_side (i : Fin 3) :
    coveringFilter G ≤ Filter.map (side G i) (triangleFilter G) := by
  classical
  intro S hS
  change (side G i) ⁻¹' S ∈ triangleFilter G at hS
  obtain ⟨T,hT,hTc,hsub⟩ := Filter.mem_countableGenerate_iff.mp hS
  letI : Countable T := hTc.to_subtype
  choose H hH hEq using fun t : T => hT t.property
  have htri : ∀ t : Triangle G, (∀ j : T, t ∈ avoidTriangle G (H j)) → side G i t ∈ S := by
    intro t ht
    apply hsub
    intro s hs
    have he := hEq ⟨s,hs⟩
    change s = _ at he
    rw [he]
    exact ht ⟨s,hs⟩
  let bad (a b : V) : Prop := ∃ h : G.Adj a b, (⟨(a,b),h⟩ : Edge G) ∉ S
  let R : SimpleGraph V :=
    { Adj := fun a b => G.Adj a b ∧ (∀ j : T, ¬(H j).Adj a b) ∧ (bad a b ∨ bad b a)
      symm := fun a b h => ⟨h.1.symm,fun j hj => h.2.1 j hj.symm,h.2.2.symm⟩
      loopless := fun a h => G.loopless a h.1 }
  have hR : R.CliqueFree 3 := by
    intro s hs
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
    have ha : (⟨(a,b),hab.1⟩ : Edge G) ∈ S :=
      side_of_triangle G H i S htri a b c hab.1 hac.1 hbc.1 hab.2.1 hac.2.1 hbc.2.1
    have hb : (⟨(b,a),hab.1.symm⟩ : Edge G) ∈ S :=
      side_of_triangle G H i S htri b a c hab.1.symm hbc.1 hac.1
        (fun j h => hab.2.1 j h.symm) hbc.2.1 hac.2.1
    rcases hab.2.2 with ⟨_,hn⟩ | ⟨_,hn⟩
    · exact hn ha
    · exact hn hb
  have hall : ∀ᶠ e : Edge G in coveringFilter G, ∀ j : T, ¬(H j).Adj e.val.1 e.val.2 :=
    eventually_countable_forall.mpr (fun j => coveringFilter_avoids G (H j) (hH j))
  filter_upwards [hall,coveringFilter_avoids G R hR] with e he hn
  by_contra hnot
  exact hn ⟨e.property,he,Or.inl ⟨e.property,hnot⟩⟩

/-- All THREE edge marginals are exactly the canonical avoiding edge filter. -/
theorem map_side (i : Fin 3) :
    Filter.map (side G i) (triangleFilter G) = coveringFilter G :=
  le_antisymm (map_side_le G i) (le_map_side G i)

/-- The triangle coupling is proper precisely when the graph is not
countably coverable. No K4-free example is asserted to have this property. -/
theorem triangleFilter_neBot_iff :
    (triangleFilter G).NeBot ↔ ¬IsCountableUnionOfTriangleFree G := by
  rw [← coveringFilter_neBot_iff G,← map_side G 0]
  exact (Filter.map_neBot_iff (side G 0)).symm


/-- This is the unrestricted filter coupling of the three copies of F,
not a hidden choice of an ultrafilter or a stronger completeness assumption. -/
theorem triangleFilter_eq_inf :
    triangleFilter G = Filter.comap (side G 0) (coveringFilter G) ⊓
      Filter.comap (side G 1) (coveringFilter G) ⊓
      Filter.comap (side G 2) (coveringFilter G) := by
  apply le_antisymm
  · exact le_inf (le_inf
      (Filter.map_le_iff_le_comap.mp (map_side_le G 0))
      (Filter.map_le_iff_le_comap.mp (map_side_le G 1)))
      (Filter.map_le_iff_le_comap.mp (map_side_le G 2))
  · apply Filter.le_countableGenerate_iff_of_countableInterFilter.mpr
    rintro s ⟨H,hH,rfl⟩
    have hmem (i : Fin 3) :
        {t : Triangle G | ¬H.Adj (side G i t).val.1 (side G i t).val.2} ∈
          Filter.comap (side G i) (coveringFilter G) :=
      Filter.preimage_mem_comap (coveringFilter_avoids G H hH)
    exact Filter.mem_of_superset
      (Filter.inter_mem_inf (Filter.inter_mem_inf (hmem 0) (hmem 1)) (hmem 2))
      (fun _ h => ⟨h.1.1,h.1.2,h.2⟩)

#print axioms triangleFilter_eq_inf



namespace Fiber
variable {A B C : Type*} (f : A → C) (g : B → C)
    (P : Filter A) (Q : Filter B)

abbrev Carrier := {x : A × B // f x.1 = g x.2}

def filter : Filter (Carrier f g) := Filter.comap Subtype.val (P ×ˢ Q)

def left (x : Carrier f g) : A := x.val.1
def right (x : Carrier f g) : B := x.val.2

instance [CountableInterFilter P] [CountableInterFilter Q] :
    CountableInterFilter (filter f g P Q) := by
  haveI : CountableInterFilter (P ×ˢ Q) :=
    inferInstanceAs (CountableInterFilter (Filter.comap Prod.fst P ⊓ Filter.comap Prod.snd Q))
  exact inferInstanceAs (CountableInterFilter (Filter.comap Subtype.val (P ×ˢ Q)))

/-- Equal marginals permit gluing filters over the common coordinate,
without any ultrafilter hypothesis. -/
theorem map_left (h : Filter.map f P = Filter.map g Q) :
    Filter.map (left f g) (filter f g P Q) = P := by
  apply le_antisymm
  · intro S hS
    change (left f g) ⁻¹' S ∈ Filter.comap Subtype.val (P ×ˢ Q)
    exact Filter.mem_comap.mpr ⟨S ×ˢ univ,Filter.prod_mem_prod hS Filter.univ_mem,
      fun _ hx => hx.1⟩
  · intro S hS
    obtain ⟨U,hU,hsub⟩ := Filter.mem_comap.mp hS
    obtain ⟨L,hL,R,hR,hrect⟩ := Filter.mem_prod_iff.mp hU
    have him : g '' R ∈ Filter.map f P := h.symm ▸ Filter.image_mem_map hR
    filter_upwards [hL,him] with a ha hag
    obtain ⟨b,hb,he⟩ := hag
    exact hsub (a := ⟨(a,b),he.symm⟩) (hrect ⟨ha,hb⟩)

theorem map_right (h : Filter.map f P = Filter.map g Q) :
    Filter.map (right f g) (filter f g P Q) = Q := by
  apply le_antisymm
  · intro S hS
    change (right f g) ⁻¹' S ∈ Filter.comap Subtype.val (P ×ˢ Q)
    exact Filter.mem_comap.mpr ⟨univ ×ˢ S,Filter.prod_mem_prod Filter.univ_mem hS,
      fun _ hx => hx.2⟩
  · intro S hS
    obtain ⟨U,hU,hsub⟩ := Filter.mem_comap.mp hS
    obtain ⟨L,hL,R,hR,hrect⟩ := Filter.mem_prod_iff.mp hU
    have him : f '' L ∈ Filter.map g Q := h ▸ Filter.image_mem_map hL
    filter_upwards [hR,him] with b hb hbf
    obtain ⟨a,ha,he⟩ := hbf
    exact hsub (a := ⟨(a,b),he⟩) (hrect ⟨ha,hb⟩)

theorem neBot [P.NeBot] (h : Filter.map f P = Filter.map g Q) :
    (filter f g P Q).NeBot := by
  apply (Filter.map_neBot_iff (left f g)).mp
  rw [map_left f g P Q h]
  infer_instance
end Fiber

/-- Two triangles with the same first oriented edge. The opposite vertices
are allowed to coincide; no unsupported distinctness claim is made. -/
abbrev Diamond := Fiber.Carrier (side G 0) (side G 0)

def diamondFilter : Filter (Diamond G) :=
  Fiber.filter (side G 0) (side G 0) (triangleFilter G) (triangleFilter G)

instance : CountableInterFilter (diamondFilter G) :=
  inferInstanceAs (CountableInterFilter
    (Fiber.filter (side G 0) (side G 0) (triangleFilter G) (triangleFilter G)))

theorem diamond_first :
    Filter.map (fun d : Diamond G => d.val.1) (diamondFilter G) = triangleFilter G :=
  Fiber.map_left _ _ _ _ rfl

theorem diamond_second :
    Filter.map (fun d : Diamond G => d.val.2) (diamondFilter G) = triangleFilter G :=
  Fiber.map_right _ _ _ _ rfl

theorem diamond_neBot (hG : ¬IsCountableUnionOfTriangleFree G) :
    (diamondFilter G).NeBot := by
  letI := (triangleFilter_neBot_iff G).mpr hG
  exact Fiber.neBot _ _ _ _ rfl

/-- The missing edge is in fact forbidden, not provided by gluing. -/
theorem opposite_nonadjacent (hG : G.CliqueFree 4) (d : Diamond G) :
    ¬G.Adj d.val.1.c d.val.2.c := by
  have ha : d.val.1.a = d.val.2.a := congrArg (fun e : Edge G => e.val.1) d.property
  have hb : d.val.1.b = d.val.2.b := congrArg (fun e : Edge G => e.val.2) d.property
  intro hcd
  have had : G.Adj d.val.1.a d.val.2.c := by simpa only [ha] using d.val.2.ac
  have hbd : G.Adj d.val.1.b d.val.2.c := by simpa only [hb] using d.val.2.bc
  exact no_adj_common_neighbors hG d.val.1.ab d.val.1.ac d.val.1.bc had hbd hcd

/-- With a proper coupling, even an eventual assertion of the opposite
adjacency would be contradictory. -/
theorem not_eventually_opposite_adjacent (hG : G.CliqueFree 4)
    (hn : ¬IsCountableUnionOfTriangleFree G) :
    ¬∀ᶠ d : Diamond G in diamondFilter G, G.Adj d.val.1.c d.val.2.c := by
  letI := diamond_neBot G hn
  intro h
  obtain ⟨d,hd⟩ := h.exists
  exact opposite_nonadjacent G hG d hd

#print axioms Fiber.map_left
#print axioms diamond_neBot
#print axioms opposite_nonadjacent
#print axioms not_eventually_opposite_adjacent


#print axioms map_side
#print axioms triangleFilter_neBot_iff
end Erdos595TriangleFilterCoupling
