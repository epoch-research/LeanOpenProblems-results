import Submission.Work
import Submission.CutBranches

/-! At most three components after deleting a vertex of a smallest failure. -/
open SimpleGraph Erdos583Work
namespace Erdos583CutComponentBoundDevelopment
open Erdos583Work.VertexCritical Erdos583CutBranchesDevelopment
open scoped Classical
set_option maxHeartbeats 1600000

def deletedComponentSet {V : Type*} {G : SimpleGraph V} (u : V)
    (C : (G.induce ({u}ᶜ : Set V)).ConnectedComponent) : Set V :=
  Subtype.val '' C.supp

lemma root_not_in_component {V : Type*} {G : SimpleGraph V} (u : V)
    (C : (G.induce ({u}ᶜ : Set V)).ConnectedComponent) : u ∉ deletedComponentSet u C := by
  rintro ⟨x,_,he⟩
  exact x.property he

lemma component_set_nonempty {V : Type*} {G : SimpleGraph V} (u : V)
    (C : (G.induce ({u}ᶜ : Set V)).ConnectedComponent) : (deletedComponentSet u C).Nonempty :=
  C.nonempty_supp.image _

lemma component_sets_disjoint {V : Type*} {G : SimpleGraph V} (u : V)
    {C D : (G.induce ({u}ᶜ : Set V)).ConnectedComponent} (hne : C ≠ D) :
    Disjoint (deletedComponentSet u C) (deletedComponentSet u D) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨a,ha,hax⟩ ⟨b,hb,hbx⟩
  have he : a=b := Subtype.ext (hax.trans hbx.symm)
  subst b
  exact hne (ConnectedComponent.eq_of_common_vertex ha hb)

lemma component_set_closed {V : Type*} {G : SimpleGraph V} (u : V)
    (C : (G.induce ({u}ᶜ : Set V)).ConnectedComponent) :
    ∀ x ∈ deletedComponentSet u C, ∀ y, G.Adj x y → y=u ∨ y ∈ deletedComponentSet u C := by
  rintro x ⟨a,ha,rfl⟩ y hxy
  by_cases hy : y=u
  · exact Or.inl hy
  · exact Or.inr ⟨⟨y,hy⟩,(C.mem_supp_congr_adj (show (G.induce ({u}ᶜ : Set V)).Adj a ⟨y,hy⟩ from hxy)).mp ha,rfl⟩

lemma singleton_component_leaf {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.Connected) (u : V) (C : (G.induce ({u}ᶜ : Set V)).ConnectedComponent)
    (hC : (deletedComponentSet u C).ncard=1) :
    ∃ x ∈ deletedComponentSet u C, G.Adj x u ∧ ∀ y, G.Adj x y → y=u := by
  obtain ⟨x,hx⟩ := Set.ncard_eq_one.mp hC
  have hxm : x ∈ deletedComponentSet u C := by rw [hx]; rfl
  have hxu : x ≠ u := fun he ↦ root_not_in_component u C (he ▸ hxm)
  letI : Nontrivial V := ⟨⟨x,u,hxu⟩⟩
  have hleaf (y : V) (hy : G.Adj x y) : y=u := by
    rcases component_set_closed u C x hxm y hy with hh|hh
    · exact hh
    · have hyx : y=x := (show y ∈ ({x} : Set V) from hx ▸ hh)
      exact (hy.ne hyx.symm).elim
  obtain ⟨a,ha⟩ := G.mem_support.mp (show x ∈ G.support from
    hG.preconnected.support_eq_univ.symm ▸ Set.mem_univ x)
  exact ⟨x,hxm,hleaf a ha ▸ ha,hleaf⟩

lemma at_most_one_singleton_component {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (u : Fin n) :
    (Finset.univ.filter fun C : (G.induce ({u}ᶜ : Set (Fin n))).ConnectedComponent ↦
      (deletedComponentSet u C).ncard=1).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro C hC D hD
  by_contra hne
  obtain ⟨x,hx,hxu,hxl⟩ := singleton_component_leaf hG u C (Finset.mem_filter.mp hC).2
  obtain ⟨y,hy,hyu,hyl⟩ := singleton_component_leaf hG u D (Finset.mem_filter.mp hD).2
  have hxy : x ≠ y := by
    intro he
    exact Set.disjoint_left.mp (component_sets_disjoint u hne) hx (he ▸ hy)
  exact (LeafPairReduction.leaf_neighbors_bridge_of_failure hsmall hG hfail hxy hxu hyu hxl hyl).1 rfl

lemma at_most_two_nonsingleton_components {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (u : Fin n) :
    (Finset.univ.filter fun C : (G.induce ({u}ᶜ : Set (Fin n))).ConnectedComponent ↦
      (deletedComponentSet u C).ncard≠1).card ≤ 2 := by
  classical
  by_contra hn
  obtain ⟨C,hC,D,hD,E,hE,hCD,hCE,hDE⟩ := Finset.two_lt_card.mp (by omega :
    2 < (Finset.univ.filter fun C : (G.induce ({u}ᶜ : Set (Fin n))).ConnectedComponent ↦
      (deletedComponentSet u C).ncard≠1).card)
  have hpos (X : (G.induce ({u}ᶜ : Set (Fin n))).ConnectedComponent) :
      0 < (deletedComponentSet u X).ncard := (Set.ncard_pos (Set.toFinite _)).mpr (component_set_nonempty u X)
  have hCsize : 2 ≤ (deletedComponentSet u C).ncard := by have := hpos C; have := (Finset.mem_filter.mp hC).2; omega
  have hDsize : 2 ≤ (deletedComponentSet u D).ncard := by have := hpos D; have := (Finset.mem_filter.mp hD).2; omega
  have hEsize : 2 ≤ (deletedComponentSet u E).ncard := by have := hpos E; have := (Finset.mem_filter.mp hE).2; omega
  have hc := two_nontrivial_branches_exhaust hsmall hG hfail (deletedComponentSet u C) (deletedComponentSet u D) u
    (root_not_in_component u C) (root_not_in_component u D) (component_sets_disjoint u hCD)
    (component_set_closed u C) (component_set_closed u D) hCsize hDsize
  have hsub : deletedComponentSet u E ⊆ (insert u (deletedComponentSet u C ∪ deletedComponentSet u D))ᶜ := by
    intro x hx hh
    rcases hh with hxu|hC|hD
    · exact root_not_in_component u E (hxu ▸ hx)
    · exact Set.disjoint_left.mp (component_sets_disjoint u hCE) hC hx
    · exact Set.disjoint_left.mp (component_sets_disjoint u hDE) hD hx
  have hh := Set.ncard_mono hsub
  omega

lemma at_most_three_components_after_delete_vertex {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (u : Fin n) :
    Nat.card (G.induce ({u}ᶜ : Set (Fin n))).ConnectedComponent ≤ 3 := by
  classical
  have h1 := at_most_one_singleton_component hsmall hG hfail u
  have h2 := at_most_two_nonsingleton_components hsmall hG hfail u
  have he := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (G.induce ({u}ᶜ : Set (Fin n))).ConnectedComponent))
    (fun C ↦ (deletedComponentSet u C).ncard=1)
  rw [Finset.card_univ,←Nat.card_eq_fintype_card] at he
  simp only [ne_eq] at h1 h2 he
  omega

lemma three_components_imply_leaf_at_vertex {n : ℕ} (hsmall : SmallerOrders n)
    {G : SimpleGraph (Fin n)} (hG : G.Connected)
    (hfail : ¬∃ D : Finset G.Subgraph, GoodDecomposition G D ∧
      D.card ≤ ⌈(Fintype.card (Fin n) : ℚ)/2⌉₊) (u : Fin n)
    (hthree : Nat.card (G.induce ({u}ᶜ : Set (Fin n))).ConnectedComponent=3) :
    ∃ x, G.Adj x u ∧ ∀ y, G.Adj x y → y=u := by
  classical
  have h2 := at_most_two_nonsingleton_components hsmall hG hfail u
  have he := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (G.induce ({u}ᶜ : Set (Fin n))).ConnectedComponent))
    (fun C ↦ (deletedComponentSet u C).ncard=1)
  rw [Finset.card_univ,←Nat.card_eq_fintype_card,hthree] at he
  simp only [ne_eq] at h2 he
  obtain ⟨C,hC⟩ := Finset.card_pos.mp (show 0 <
    (Finset.univ.filter fun C : (G.induce ({u}ᶜ : Set (Fin n))).ConnectedComponent ↦
      (deletedComponentSet u C).ncard=1).card by omega)
  obtain ⟨x,_,hx,hleaf⟩ := singleton_component_leaf hG u C (Finset.mem_filter.mp hC).2
  exact ⟨x,hx,hleaf⟩

end Erdos583CutComponentBoundDevelopment
