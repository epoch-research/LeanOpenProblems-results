import Submission.Work

/-!
The ideal of vertex subsets whose induced graphs have countable triangle-free
edge covers is closed under unions indexed by at most continuum many sets.
Its dual filter is consequently continuum-successor-complete. Properness is
exactly the original non-coverability condition, and is not proved here for
any K4-free graph.
-/

set_option autoImplicit false
open SimpleGraph Set Filter
namespace Erdos595VertexCoverFilter
open Erdos595Work

variable {V : Type*} (G : SimpleGraph V)

/-- The spanning version of the induced graph on a vertex subset. -/
def span (S : Set V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ S ∧ b ∈ S
  symm := fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := fun _ h => h.1.ne rfl

def On (S : Set V) : Prop := IsCountableUnionOfTriangleFree (span G S)

lemma cover_bot : IsCountableUnionOfTriangleFree (⊥ : SimpleGraph V) :=
  ⟨fun _ => ⊥,fun _ => SimpleGraph.cliqueFree_bot (by decide),by simp⟩

lemma On.mono {S T : Set V} (hT : On G T) (hST : S ⊆ T) : On G S :=
  countable_union_of_hom
    (show span G S →g span G T from
      ⟨id,fun h => ⟨h.1,hST h.2.1,hST h.2.2⟩⟩) hT

lemma on_empty : On G ∅ := by
  have he : span G ∅ = ⊥ := by ext a b; simp [span]
  rw [On,he]
  exact cover_bot

lemma on_univ_iff : On G univ ↔ IsCountableUnionOfTriangleFree G := by
  have he : span G univ = G := by ext a b; simp [span]
  rw [On,he]

lemma on_iff_induce (S : Set V) :
    On G S ↔ IsCountableUnionOfTriangleFree (G.induce S) := by
  classical
  constructor
  · intro h
    exact countable_union_of_hom
      (show G.induce S →g span G S from
        ⟨Subtype.val,fun {a b} h => ⟨h,a.property,b.property⟩⟩) h
  · intro h
    by_cases hS : S.Nonempty
    · let v₀ : S := ⟨hS.choose,hS.choose_spec⟩
      let f (v : V) : S := if hv : v ∈ S then ⟨v,hv⟩ else v₀
      apply countable_union_of_hom (G := span G S) (H := G.induce S) (f := ?_) h
      refine ⟨f,?_⟩
      intro a b hab
      change G.Adj (f a).val (f b).val
      simpa only [f,dif_pos hab.2.1,dif_pos hab.2.2] using hab.1
    · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
      subst S
      exact on_empty G

/-- No restriction on the carrier of G is required; only the index family
has an injection into binary sequences. -/
theorem on_iUnion {I : Type*} (e : I ↪ (ℕ → Fin 2))
    (S : I → Set V) (hS : ∀ i, On G (S i)) : On G (⋃ i, S i) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hi => simpa only [Set.iUnion_of_empty] using on_empty G
  | inr hi =>
    let i₀ : I := Classical.arbitrary I
    let pick (v : V) : I := if h : ∃ i, v ∈ S i then h.choose else i₀
    have hpick (v : V) (hv : v ∈ ⋃ i, S i) : v ∈ S (pick v) := by
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hv
      have he : ∃ i, v ∈ S i := ⟨i,hi⟩
      simpa only [pick,dif_pos he] using he.choose_spec
    let f : V → ℕ → Fin 2 := fun v => e (pick v)
    apply countable_union_of_vertex_pieces (span G (⋃ i, S i)) f
    intro z
    by_cases hz : ∃ i, e i = z
    · obtain ⟨i,rfl⟩ := hz
      apply countable_union_of_hom (G := vertexPiece (span G (⋃ i, S i)) f (e i))
        (H := span G (S i)) (f := ?_) (hS i)
      refine ⟨id,?_⟩
      intro a b hab
      have ha : pick a = i := e.injective hab.2.1
      have hb : pick b = i := e.injective hab.2.2
      exact ⟨hab.1.1,ha ▸ hpick a hab.1.2.1,hb ▸ hpick b hab.1.2.2⟩
    · apply countable_union_of_hom (G := vertexPiece (span G (⋃ i, S i)) f z)
        (H := (⊥ : SimpleGraph V)) (f := ?_) cover_bot
      exact ⟨id,fun {a b} hab => (hz ⟨pick a,hab.2.1⟩).elim⟩

section TypeZero
variable {A : Type} (K : SimpleGraph A)

lemma binary_embedding {I : Type} (hI : Cardinal.mk I ≤ Cardinal.continuum) :
    Nonempty (I ↪ (ℕ → Fin 2)) := by
  apply Cardinal.lift_mk_le'.mp
  simpa only [Cardinal.lift_uzero,Cardinal.mk_arrow,Cardinal.mk_fin,
    Cardinal.mk_nat,Nat.cast_ofNat,Cardinal.two_power_aleph0] using hI

lemma on_sUnion (S : Set (Set A)) (hcard : Cardinal.mk S < Order.succ Cardinal.continuum)
    (hS : ∀ s ∈ S, On K s) : On K (⋃₀ S) := by
  obtain ⟨e⟩ := binary_embedding (Order.le_of_lt_succ hcard)
  have h := on_iUnion K e (fun s : S => s.val) (fun s => hS s s.property)
  simpa only [Set.iUnion_subtype,Set.sUnion_eq_biUnion] using h

private lemma two_lt_bound : (2 : Cardinal) < Order.succ Cardinal.continuum :=
  (Cardinal.nat_lt_continuum 2).trans (Order.lt_succ _)

/-- Dual to the ideal of coverable induced vertex sets. This is NOT an
ultrafilter, and no extension preserving completeness is asserted. -/
def vertexFilter : Filter A :=
  Filter.ofCardinalUnion {S | On K S} two_lt_bound (on_sUnion K)
    (fun _ hT _ hST => On.mono K hT hST)

instance : CardinalInterFilter (vertexFilter K) (Order.succ Cardinal.continuum) :=
  inferInstanceAs (CardinalInterFilter (Filter.ofCardinalUnion _ _ _ _) _)

instance : CountableInterFilter (vertexFilter K) :=
  CardinalInterFilter.toCountableInterFilter _
    (Cardinal.aleph0_lt_continuum.trans (Order.lt_succ _))

@[simp] lemma mem_vertexFilter (S : Set A) :
    S ∈ vertexFilter K ↔ On K Sᶜ := Iff.rfl

lemma proper_iff : (vertexFilter K).NeBot ↔ ¬IsCountableUnionOfTriangleFree K := by
  constructor
  · intro hF hK
    letI := hF
    have he : (∅ : Set A) ∈ vertexFilter K := by
      rw [mem_vertexFilter,Set.compl_empty,on_univ_iff]
      exact hK
    exact Filter.empty_notMem _ he
  · intro hn
    constructor
    intro he
    have hh : (∅ : Set A) ∈ vertexFilter K := by rw [he]; simp
    rw [mem_vertexFilter,Set.compl_empty,on_univ_iff] at hh
    exact hn hh

/-- The continuum-completeness statement in a usable indexed form. -/
theorem inter_mem {I : Type} (hI : Cardinal.mk I ≤ Cardinal.continuum)
    (S : I → Set A) (hS : ∀ i, S i ∈ vertexFilter K) :
    (⋂ i, S i) ∈ vertexFilter K :=
  (Filter.cardinal_iInter_mem (Order.lt_succ_of_le hI)).mpr hS

/-- Every large vertex set is still non-coverable. -/
theorem large_no_cover [NeBot (vertexFilter K)] (S : Set A)
    (hS : S ∈ vertexFilter K) : ¬On K S := by
  intro h
  have hc : Sᶜ ∈ vertexFilter K := by simpa only [mem_vertexFilter,compl_compl] using h
  obtain ⟨a,ha,hn⟩ := Filter.nonempty_of_mem (Filter.inter_mem hS hc)
  exact hn ha

/-- In a K4-free graph, each original neighborhood is a small vertex set. -/
lemma neighborhood_small (hK : K.CliqueFree 4) (v : A) : On K (K.neighborSet v) := by
  classical
  have ht : (span K (K.neighborSet v)).CliqueFree 3 := by
    intro s hs
    obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp hs
    exact no_adj_common_neighbors hK hab.2.1 hab.2.2 hab.1 hac.2.2 hac.1 hbc.1
  exact ⟨fun _ => span K (K.neighborSet v),fun _ => ht,by simp⟩

/-- Simultaneously avoid the neighborhoods of any continuum-sized detector
family. This is a vertex-filter assertion, not an upgrade of the edge filter. -/
theorem avoids_neighborhood_family {I : Type}
    (hK : K.CliqueFree 4) (hI : Cardinal.mk I ≤ Cardinal.continuum) (d : I → A) :
    ∀ᶠ v in vertexFilter K, ∀ i, ¬K.Adj (d i) v := by
  apply (Filter.eventually_cardinal_forall (Order.lt_succ_of_le hI)).mpr
  intro i
  change (K.neighborSet (d i))ᶜ ∈ vertexFilter K
  simpa only [mem_vertexFilter,compl_compl] using neighborhood_small K hK (d i)

end TypeZero
#print axioms on_iUnion
#print axioms proper_iff
#print axioms inter_mem
#print axioms large_no_cover
#print axioms avoids_neighborhood_family
end Erdos595VertexCoverFilter
