import Submission.NoetherianNeighborhoods
import Submission.NoCountableK4Target

/-!
Finite common-neighborhood determination together with the finite independent-set
extension property imposes a finite edge palette on a countable K4-free graph.
This is a structural restriction, not a settlement of Erdos 595.
-/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595FiniteCommonIndependent
open Erdos595Work Erdos595Noetherian Erdos595BadEdge

variable {V : Type*}

def FiniteIndependentExtension (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, (∀ a ∈ s, ∀ b ∈ s, ¬G.Adj a b) →
    ∃ w : V, ∀ a ∈ s, G.Adj a w

/-- Finite determination upgrades finite independent requests to arbitrary ones. -/
theorem independent_extension (G : SimpleGraph V) (hfin : FiniteCommonNeighbors G)
    (hext : FiniteIndependentExtension G) (S : Set V)
    (hS : ∀ a ∈ S, ∀ b ∈ S, ¬G.Adj a b) :
    ∃ w : V, ∀ a ∈ S, G.Adj a w := by
  classical
  obtain ⟨t,ht⟩ := hfin S
  let s := t.image Subtype.val
  obtain ⟨w,hw⟩ := hext s (by
    rintro a ha b hb
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hb
    exact hS a a.property b b.property)
  exact ⟨w,(ht w).mp (fun a ha => hw a (Finset.mem_image.mpr ⟨a,ha,rfl⟩))⟩

/-- No finite-palette obstruction can coexist with both properties on a countable
K4-free graph. There is no uniform bound on the finite palette asserted here. -/
theorem countable_finite_cover [Countable V] (G : SimpleGraph V)
    (hG : G.CliqueFree 4) (hfin : FiniteCommonNeighbors G)
    (hext : FiniteIndependentExtension G) : FiniteCover G := by
  classical
  by_contra hn
  apply Erdos595NoCountableK4Target.no_countable_target G hG hn G
    SimpleGraph.Hom.id (fun S hS => ?_) G hG ⟨SimpleGraph.Hom.id⟩
  obtain ⟨w,hw⟩ := independent_extension G hfin hext S hS
  exact ⟨w,fun a ha => (hw a ha).symm⟩

/-- Finite determination is inherited by induced subgraphs. -/
theorem finite_common_induce (G : SimpleGraph V) (hfin : FiniteCommonNeighbors G)
    (S : Set V) : FiniteCommonNeighbors (G.induce S) := by
  classical
  intro T
  let U : Set V := Subtype.val '' T
  obtain ⟨t,ht⟩ := hfin U
  have hex (v : U) : ∃ a : T, a.val.val = v.val := by
    obtain ⟨a,ha,he⟩ := v.property
    exact ⟨⟨a,ha⟩,he⟩
  choose f hf using hex
  refine ⟨t.image f,fun w => ⟨?_,?_⟩⟩
  · intro hw a ha
    apply (ht w.val).mp (fun v hv => ?_) a.val ⟨a,ha,rfl⟩
    have h := hw (f v) (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
    change G.Adj (f v).val.val w.val at h
    simpa only [hf] using h
  · intro hw a _
    exact hw a.val a.property

/-- A finitary operation has a countable closed superset of each countable set. -/
theorem countable_closed_superset (f : Finset V → V) (C : Set V) (hC : C.Countable) :
    ∃ S : Set V, S.Countable ∧ C ⊆ S ∧
      ∀ t : Finset V, (↑t : Set V) ⊆ S → f t ∈ S := by
  classical
  let step : Set V → Set V := fun S => S ∪ f '' {t : Finset V | (↑t : Set V) ⊆ S}
  have hc (S : Set V) (hS : S.Countable) : (step S).Countable := by
    have ht : {t : Finset V | (↑t : Set V) ⊆ S}.Countable := by
      apply ((Set.countable_setOf_finite_subset hS).preimage
        (Finset.coe_injective : Function.Injective (fun t : Finset V => (↑t : Set V)))).mono
      intro t ht
      exact ⟨t.finite_toSet,ht⟩
    exact hS.union (ht.image f)
  let X : ℕ → Set V := fun n => step^[n] C
  have hx (n : ℕ) : X (n+1) = step (X n) := Function.iterate_succ_apply' step n C
  have hxc (n : ℕ) : (X n).Countable := by
    induction n with
    | zero => exact hC
    | succ n ih => rw [hx]; exact hc _ ih
  have hm : Monotone X := monotone_nat_of_le_succ (fun n => by
    rw [hx]; exact Set.subset_union_left)
  refine ⟨⋃ n, X n,Set.countable_iUnion hxc,?_,?_⟩
  · exact Set.subset_iUnion X 0
  · intro t ht
    obtain ⟨n,hn⟩ := hm.directed_le.exists_mem_subset_of_finset_subset_biUnion ht
    apply Set.mem_iUnion.mpr
    refine ⟨n+1,?_⟩
    rw [hx]
    exact Or.inr ⟨t,hn,rfl⟩

/-- Close a countable set under chosen witnesses to finite independent requests. -/
theorem countable_extension_hull (G : SimpleGraph V) (hext : FiniteIndependentExtension G)
    (C : Set V) (hC : C.Countable) :
    ∃ S : Set V, S.Countable ∧ C ⊆ S ∧ FiniteIndependentExtension (G.induce S) := by
  classical
  obtain ⟨w₀,_⟩ := hext ∅ (by simp)
  let m : Finset V → V := fun t =>
    if h : ∀ a ∈ t, ∀ b ∈ t, ¬G.Adj a b then (hext t h).choose else w₀
  have hm (t : Finset V) (h : ∀ a ∈ t, ∀ b ∈ t, ¬G.Adj a b) :
      ∀ a ∈ t, G.Adj a (m t) := by
    simpa only [m,dif_pos h] using (hext t h).choose_spec
  obtain ⟨S,hS,hCS,hclosed⟩ := countable_closed_superset m C hC
  refine ⟨S,hS,hCS,?_⟩
  intro t ht
  let t' := t.image Subtype.val
  have ht' : ∀ a ∈ t', ∀ b ∈ t', ¬G.Adj a b := by
    rintro a ha b hb
    obtain ⟨x,hx,hxa⟩ := Finset.mem_image.mp ha
    obtain ⟨y,hy,hyb⟩ := Finset.mem_image.mp hb
    rw [← hxa,← hyb]
    exact ht x hx y hy
  have hsub : (↑t' : Set V) ⊆ S := by
    rintro a ha
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp ha
    exact a.property
  exact ⟨⟨m t',hclosed t' hsub⟩,fun a ha =>
    hm t' ht' a.val (Finset.mem_image.mpr ⟨a,ha,rfl⟩)⟩

open Erdos595FinitePalette

lemma finite_cover_of_coloring {C : Type*} [Finite C] (G : SimpleGraph V)
    (h : HasColoring G C) : FiniteCover G := by
  classical
  letI := Fintype.ofFinite C
  obtain ⟨c,hc⟩ := h
  let H : C → SimpleGraph V := fun k =>
    { Adj a b := G.Adj a b ∧ c s(a,b) = k
      symm := fun _ _ h => ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2⟩
      loopless := fun _ h => G.loopless _ h.1 }
  have hh (k : C) : (H k).CliqueFree 3 := by
    intro t ht
    obtain ⟨a,b,d,hab,had,hbd,_⟩ := SimpleGraph.is3Clique_iff.mp ht
    exact hc a b d hab.1 had.1 hbd.1
      ⟨hab.2.trans had.2.symm,hab.2.trans hbd.2.symm⟩
  refine ⟨Fintype.card C,fun i => H ((Fintype.equivFin C).symm i),fun _ => hh _,?_⟩
  intro a b hab
  exact ⟨Fintype.equivFin C (c s(a,b)),hab,by simp⟩

/-- Failure of finite edge-coverability has a countable induced witness.
This uses finite-palette compactness, not countable-palette compactness. -/
theorem countable_witness (G : SimpleGraph V) (hn : ¬FiniteCover G) :
    ∃ S : Set V, S.Countable ∧ ¬FiniteCover (G.induce S) := by
  classical
  have hex (n : ℕ) : ∃ s : Finset V,
      ¬HasColoring (G.induce (↑s : Set V)) (Option (Fin n)) := by
    by_contra h
    push_neg at h
    exact hn (finite_cover_of_coloring G (compactness G h))
  choose s hs using hex
  let S : Set V := ⋃ n, (↑(s n) : Set V)
  refine ⟨S,Set.countable_iUnion (fun n => (s n).countable_toSet),?_⟩
  intro h
  obtain ⟨n,hc⟩ := Erdos595NoCountableK4Target.finiteCover_coloring h
  let f : G.induce (↑(s n) : Set V) →g G.induce S :=
    ⟨fun a => ⟨a.val,Set.mem_iUnion.mpr ⟨n,a.property⟩⟩,fun h => h⟩
  exact hs n (hc.comap f)

/-- The countable conclusion reflects to arbitrary cardinalities by a countable
extension-closed hull. Both hypotheses on neighborhoods are essential to this
argument; K4-freeness alone is not shown to suffice. -/
theorem finite_cover (G : SimpleGraph V) (hG : G.CliqueFree 4)
    (hfin : FiniteCommonNeighbors G) (hext : FiniteIndependentExtension G) :
    FiniteCover G := by
  classical
  by_contra hn
  obtain ⟨C,hC,hnC⟩ := countable_witness G hn
  obtain ⟨S,hS,hCS,hSE⟩ := countable_extension_hull G hext C hC
  letI : Countable S := hS.to_subtype
  have hSG : (G.induce S).CliqueFree 4 := hG.comap (SimpleGraph.Embedding.induce S)
  obtain ⟨n,hcol⟩ := Erdos595NoCountableK4Target.finiteCover_coloring
    (countable_finite_cover (G.induce S) hSG (finite_common_induce G hfin S) hSE)
  let f : G.induce C →g G.induce S := ⟨fun a => ⟨a.val,hCS a.property⟩,fun h => h⟩
  exact hnC (finite_cover_of_coloring (G.induce C) (hcol.comap f))

#print axioms independent_extension
#print axioms countable_finite_cover
#print axioms countable_extension_hull
#print axioms countable_witness
#print axioms finite_cover
end Erdos595FiniteCommonIndependent
