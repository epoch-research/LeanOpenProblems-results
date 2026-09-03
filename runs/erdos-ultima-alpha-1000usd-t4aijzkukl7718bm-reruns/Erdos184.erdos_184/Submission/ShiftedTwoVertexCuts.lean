import Submission.TwoTerminalGluing

/-!
Two-vertex separation reductions for the shifted bound. All gluing uses
only one complementary path per side.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.TwoTerminalGluing

variable {V : Type*} [Fintype V]

lemma even_degree_of_even_else (A : SimpleGraph V) (a : V)
    (he : ∀ x, x ≠ a → Even (A.degree x)) : Even (A.degree a) := by
  have hs : Even (∑ x ∈ (Finset.univ : Finset V).erase a, A.degree x) :=
    Finset.even_sum _ (fun x hx => he x (Finset.mem_erase.mp hx).1)
  have ht : Even (∑ x, A.degree x) := by
    rw [A.sum_degrees_eq_twice_card_edges]
    exact even_two_mul _
  rw [← Finset.add_sum_erase (Finset.univ : Finset V) (fun x => A.degree x)
    (Finset.mem_univ a)] at ht
  exact (Nat.even_add.mp ht).mpr hs

lemma parity_of_two_vertex_separation {G A B : SimpleGraph V} {a b : V}
    (heG : ∀ x, Even (G.degree x))
    (hd : Disjoint A.edgeSet B.edgeSet) (hu : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hv : A.support ∩ B.support ⊆ {a,b}) :
    ((∀ x, Even (A.degree x)) ∧ (∀ x, Even (B.degree x))) ∨
      ((∀ x, Even (A.degree x) ↔ x ≠ a ∧ x ≠ b) ∧
       (∀ x, Even (B.degree x) ↔ x ≠ a ∧ x ≠ b)) := by
  have heq : A ⊔ B = G := edgeSet_injective (by rw [edgeSet_sup,hu])
  have hpar (x : V) : Even (A.degree x) ↔ Even (B.degree x) := by
    have hh := degree_sup_of_edge_disjoint A B hd x
    have hx := heG x
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,heq] at hh hx ⊢
    rw [hh] at hx
    exact Nat.even_add.mp hx
  have hout (x : V) (hxa : x ≠ a) (hxb : x ≠ b) : Even (A.degree x) := by
    by_cases hx : x ∈ A.support
    · have hxB : x ∉ B.support := by
        intro hy
        have hh := hv ⟨hx,hy⟩
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hh
        exact hh.elim hxa hxb
      have hh := degree_eq_of_other_unsupported hu x hxB
      have hx := heG x
      simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hx ⊢
      rwa [hh]
    · rw [(A.degree_eq_zero_iff_notMem_support x).mpr hx]
      decide
  by_cases ha : Even (A.degree a)
  · have hb : Even (A.degree b) := even_degree_of_even_else A b (by
      intro x hxb
      by_cases hxa : x = a
      · subst x; exact ha
      · exact hout x hxa hxb)
    have hA : ∀ x, Even (A.degree x) := by
      intro x
      by_cases hxa : x = a
      · subst x; exact ha
      by_cases hxb : x = b
      · subst x; exact hb
      exact hout x hxa hxb
    exact Or.inl ⟨hA,fun x => (hpar x).mp (hA x)⟩
  · have hb : ¬Even (A.degree b) := by
      intro hb
      apply ha
      apply even_degree_of_even_else A a
      intro x hxa
      by_cases hxb : x = b
      · subst x; exact hb
      · exact hout x hxa hxb
    have hA : ∀ x, Even (A.degree x) ↔ x ≠ a ∧ x ≠ b := by
      intro x
      constructor
      · intro hx
        exact ⟨fun h => ha (h ▸ hx),fun h => hb (h ▸ hx)⟩
      · rintro ⟨hxa,hxb⟩
        exact hout x hxa hxb
    exact Or.inr ⟨hA,fun x => (hpar x).symm.trans (hA x)⟩

omit [Fintype V] in
lemma support_edge_eq {a b : V} (hab : a ≠ b) :
    (edge a b).support = {a,b} := by
  ext x
  simp only [mem_support,edge_adj,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨y,h,_⟩
    exact h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  · rintro (rfl | rfl)
    · exact ⟨b,Or.inl ⟨rfl,rfl⟩,hab⟩
    · exact ⟨a,Or.inr ⟨rfl,rfl⟩,hab.symm⟩

lemma degree_edge_eq {a b : V} (hab : a ≠ b) (x : V) :
    (edge a b).degree x = if x = a ∨ x = b then 1 else 0 := by
  have hm : MatchingSmoothing.IsMatching (edge a b : SimpleGraph V) := by
    intro u v w h₁ h₂
    simp only [edge_adj] at h₁ h₂
    aesop
  have hh := hm.degree_eq_indicator x
  simpa only [support_edge_eq hab,Set.mem_insert_iff,Set.mem_singleton_iff,
    ← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using hh

lemma even_sup_edge_of_odd_ends {A : SimpleGraph V} {a b : V}
    (hab : a ≠ b) (hn : ¬A.Adj a b)
    (he : ∀ x, Even (A.degree x) ↔ x ≠ a ∧ x ≠ b) :
    ∀ x, Even ((A ⊔ edge a b).degree x) := by
  have hd : Disjoint A.edgeSet (edge a b).edgeSet := by
    rw [edge_edgeSet_of_ne hab,Set.disjoint_singleton_right]
    exact hn
  intro x
  have hh := degree_sup_of_edge_disjoint A (edge a b) hd x
  have hm := degree_edge_eq hab x
  have hx := he x
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hm hx ⊢
  rw [hh,hm]
  by_cases h : x = a ∨ x = b
  · rw [if_pos h,Nat.even_add_one,hx]
    tauto
  · rw [if_neg h,Nat.add_zero,hx]
    tauto

lemma even_sdiff_edge_of_odd_ends {A : SimpleGraph V} {a b : V}
    (hab : A.Adj a b)
    (he : ∀ x, Even (A.degree x) ↔ x ≠ a ∧ x ≠ b) :
    ∀ x, Even ((A \ edge a b).degree x) := by
  have hle : edge a b ≤ A := (edge_le_iff A).mpr (Or.inr hab)
  intro x
  have hh := degree_sdiff_of_le hle x
  have hm := degree_edge_eq hab.ne x
  have hx := he x
  have hl := degree_le_of_le hle (v := x)
  simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hm hx hl ⊢
  rw [hh,hm]
  rw [hm] at hl
  by_cases h : x = a ∨ x = b
  · rw [if_pos h] at hl ⊢
    rw [Nat.even_sub hl,hx]
    simp only [Nat.not_even_one,iff_false]
    tauto
  · rw [if_neg h,Nat.sub_zero,hx]
    tauto

lemma support_sup_edge_of_odd_ends {A : SimpleGraph V} {a b : V}
    (he : ∀ x, Even (A.degree x) ↔ x ≠ a ∧ x ≠ b) :
    (A ⊔ edge a b).support ⊆ A.support := by
  have ha : a ∈ A.support := by
    apply A.degree_pos_iff_mem_support a |>.mp
    have hn : ¬Even (A.degree a) := by simp [he]
    by_contra! hz
    have hh : A.degree a = 0 := by omega
    simp [hh] at hn
  have hb : b ∈ A.support := by
    apply A.degree_pos_iff_mem_support b |>.mp
    have hn : ¬Even (A.degree b) := by simp [he]
    by_contra! hz
    have hh : A.degree b = 0 := by omega
    simp [hh] at hn
  rintro x ⟨y,hxy⟩
  rcases hxy with h | h
  · exact ⟨y,h⟩
  · rcases (edge_adj a b x y).mp h with ⟨h,_⟩
    rcases h with h | h
    · exact h.1.symm ▸ ha
    · exact h.1.symm ▸ hb

end Erdos184.TwoTerminalGluing

namespace Erdos184.ShiftedCritical
open ExactVertexSmoothing TwoTerminalGluing
universe u
variable {V : Type u} [Fintype V]

lemma IsVertexMinimal.bound_on_support_subset {C : ℕ} {G : SimpleGraph V}
    (hG : IsVertexMinimal C G) (A : SimpleGraph V) (S : Set V)
    (hs : A.support ⊆ S) (hlt : S.ncard < Fintype.card V)
    (he : ∀ x, Even (A.degree x)) : HasPieceBound (C * (S.ncard - 2)) A := by
  have hcard := Set.ncard_le_ncard hs
  obtain ⟨D,hc,hd,hb⟩ := hG.bound_on_smaller_support A (hcard.trans_lt hlt) he
  exact ⟨D,hc,hd,hb.trans (Nat.mul_le_mul_left C (Nat.sub_le_sub_right hcard 2))⟩

set_option maxHeartbeats 1200000 in
/-- A genuine two-terminal separation can be solved on its two smaller sides.
The sides need not be even initially. -/
lemma IsVertexMinimal.no_two_vertex_split {C : ℕ} {G : SimpleGraph V}
    (hG : IsVertexMinimal C G) (A B : SimpleGraph V) {a b : V} (hab : a ≠ b)
    (hA : A ≤ G) (hB : B ≤ G)
    (hdis : Disjoint A.edgeSet B.edgeSet) (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hinter : A.support ∩ B.support ⊆ {a,b})
    (hAc : 2 ≤ A.support.ncard) (hBc : 2 ≤ B.support.ncard)
    (hAl : A.support.ncard < Fintype.card V) (hBl : B.support.ncard < Fintype.card V) : False := by
  have hover : (A.support ∩ B.support).ncard ≤ 2 :=
    (Set.ncard_le_ncard hinter).trans_eq (Set.ncard_pair hab)
  have hsum := Set.ncard_union_add_ncard_inter A.support B.support
  rw [support_union_of_edge_cover hcover] at hsum
  have hs : G.support.ncard ≤ Fintype.card V := by
    simpa using Set.ncard_le_ncard (Set.subset_univ G.support)
  have hbudget : C * (A.support.ncard - 2) + C * (B.support.ncard - 2) ≤
      C * (Fintype.card V - 2) := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left C (by omega)
  have finish (X Y : SimpleGraph V) (hx : X ≤ G) (hy : Y ≤ G)
      (heX : ∀ x, Even (X.degree x)) (heY : ∀ x, Even (Y.degree x))
      (hsX : X.support ⊆ A.support) (hsY : Y.support ⊆ B.support)
      (hdXY : Disjoint X.edgeSet Y.edgeSet) (huXY : X.edgeSet ∪ Y.edgeSet = G.edgeSet) : False := by
    obtain ⟨DX,hcX,hdX,hbX⟩ := hG.bound_on_support_subset X A.support hsX hAl heX
    obtain ⟨DY,hcY,hdY,hbY⟩ := hG.bound_on_support_subset Y B.support hsY hBl heY
    obtain ⟨D,hcD,hdD,hbD⟩ := combine_pure_decompositions hx hy hdXY huXY DX DY hcX hcY hdX hdY
    exact hG.2.1 ⟨D,hcD,hdD,by omega⟩
  rcases parity_of_two_vertex_separation hG.1 hdis hcover hinter with hEven | hOdd
  · exact finish A B hA hB hEven.1 hEven.2 (Set.Subset.refl _) (Set.Subset.refl _) hdis hcover
  obtain ⟨hOddA,hOddB⟩ := hOdd
  have move (X Y : SimpleGraph V) (hX : X ≤ G) (hY : Y ≤ G)
      (hXY : Disjoint X.edgeSet Y.edgeSet) (huXY : X.edgeSet ∪ Y.edgeSet = G.edgeSet)
      (hOX : ∀ x, Even (X.degree x) ↔ x ≠ a ∧ x ≠ b)
      (hOY : ∀ x, Even (Y.degree x) ↔ x ≠ a ∧ x ≠ b)
      (hxy : X.Adj a b) :
      ∃ X' Y' : SimpleGraph V, X' ≤ G ∧ Y' ≤ G ∧
        (∀ x, Even (X'.degree x)) ∧ (∀ x, Even (Y'.degree x)) ∧
        X'.support ⊆ X.support ∧ Y'.support ⊆ Y.support ∧
        Disjoint X'.edgeSet Y'.edgeSet ∧ X'.edgeSet ∪ Y'.edgeSet = G.edgeSet := by
    have hnY : ¬Y.Adj a b := fun hy => Set.disjoint_left.mp hXY
      (show s(a,b) ∈ X.edgeSet from hxy) (show s(a,b) ∈ Y.edgeSet from hy)
    have hEdgeX : (edge a b : SimpleGraph V).edgeSet ⊆ X.edgeSet := by
      rw [edge_edgeSet_of_ne hab]
      exact Set.singleton_subset_iff.mpr hxy
    refine ⟨X \ edge a b,Y ⊔ edge a b,sdiff_le.trans hX,?_,
      ?_,?_,
      support_mono sdiff_le,support_sup_edge_of_odd_ends hOY,?_,?_⟩
    · exact sup_le hY ((edge_le_iff G).mpr (Or.inr (hX hxy)))
    · intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using even_sdiff_edge_of_odd_ends hxy hOX x
    · intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using even_sup_edge_of_odd_ends hab hnY hOY x
    · rw [edgeSet_sdiff,edgeSet_sup]
      apply Set.disjoint_left.mpr
      intro e heX heY
      exact heY.elim (fun heY => Set.disjoint_left.mp hXY heX.1 heY) heX.2
    · rw [edgeSet_sdiff,edgeSet_sup,← huXY]
      ext e
      have he : e ∈ (edge a b : SimpleGraph V).edgeSet → e ∈ X.edgeSet := fun h => hEdgeX h
      simp only [Set.mem_union,Set.mem_diff]
      tauto
  by_cases ha : A.Adj a b
  · obtain ⟨X,Y,hX,hY,heX,heY,hsX,hsY,hd,hu⟩ := move A B hA hB hdis hcover hOddA hOddB ha
    exact finish X Y hX hY heX heY hsX hsY hd hu
  by_cases hb : B.Adj a b
  · obtain ⟨Y,X,hY,hX,heY,heX,hsY,hsX,hd,hu⟩ := move B A hB hA hdis.symm
      (by simpa only [Set.union_comm] using hcover) hOddB hOddA hb
    exact finish X Y hX hY heX heY hsX hsY hd.symm (by simpa only [Set.union_comm] using hu)
  have hsA := support_sup_edge_of_odd_ends hOddA
  have hsB := support_sup_edge_of_odd_ends hOddB
  obtain ⟨DA,hcA,hdA,hbA⟩ := hG.bound_on_support_subset (A ⊔ edge a b) A.support hsA hAl
    (by
      intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using even_sup_edge_of_odd_ends hab ha hOddA x)
  obtain ⟨DB,hcB,hdB,hbB⟩ := hG.bound_on_support_subset (B ⊔ edge a b) B.support hsB hBl
    (by
      intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using even_sup_edge_of_odd_ends hab hb hOddB x)
  have hnew : (edge a b : SimpleGraph V).Adj a b := by simp [edge_adj,hab]
  have hi : (A ⊔ edge a b).support ∩ (B ⊔ edge a b).support ⊆ {a,b} :=
    fun _ h => hinter ⟨hsA h.1,hsB h.2⟩
  have hd : (A ⊔ edge a b).edgeSet ∩ (B ⊔ edge a b).edgeSet ⊆ {s(a,b)} := by
    rw [edgeSet_sup,edgeSet_sup,edge_edgeSet_of_ne hab]
    intro e he
    rcases he.1 with heA | heE
    · exact he.2.resolve_left (fun heB => Set.disjoint_left.mp hdis heA heB)
    · exact heE
  have hu : G.edgeSet = ((A ⊔ edge a b).edgeSet ∪ (B ⊔ edge a b).edgeSet) \ {s(a,b)} := by
    rw [edgeSet_sup,edgeSet_sup,edge_edgeSet_of_ne hab,← hcover]
    ext e
    by_cases he : e = s(a,b)
    · subst e
      simp [ha,hb]
    · simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff,he]
      tauto
  obtain ⟨D,hcD,hdD,hbD⟩ := glue_decompositions (G := G) (Or.inr hnew) (Or.inr hnew)
    hi hd hu DA DB hcA hcB hdA hdB
  exact hG.2.1 ⟨D,hcD,hdD,by omega⟩

set_option maxHeartbeats 800000 in
/-- A shifted vertex-minimal counterexample is three-vertex-connected:
removing any two distinct vertices preserves reachability between all others. -/
lemma IsVertexMinimal.delete_two_vertices_reachable {C : ℕ} {G : SimpleGraph V}
    (hG : IsVertexMinimal C G) (hC : 0 < C) {a b u w : V}
    (hab : a ≠ b) (hua : u ≠ a) (hub : u ≠ b) (hwa : w ≠ a) (hwb : w ≠ b) :
    ((G.deleteIncidenceSet a).deleteIncidenceSet b).Reachable u w := by
  by_contra hn
  let R := (G.deleteIncidenceSet a).deleteIncidenceSet b
  let S : Set V := {x | x = a ∨ x = b ∨ R.Reachable u x}
  let A := RankBlocks.sideGraph G S
  let B := G \ A
  have hA : A ≤ G := fun _ _ h => h.1
  have hB : B ≤ G := sdiff_le
  have huS : u ∈ S := Or.inr (Or.inr (Reachable.refl _))
  have hwS : w ∉ S := by
    rintro (h | h | h)
    · exact hwa h
    · exact hwb h
    · exact hn h
  have hclosed {x y : V} (hx : x ∈ S) (hxa : x ≠ a) (hxb : x ≠ b)
      (hxy : G.Adj x y) : y ∈ S := by
    by_cases hya : y = a
    · exact Or.inl hya
    by_cases hyb : y = b
    · exact Or.inr (Or.inl hyb)
    have hux : R.Reachable u x := (hx.resolve_left hxa).resolve_left hxb
    have hRxy : R.Adj x y := deleteIncidenceSet_adj.mpr
      ⟨deleteIncidenceSet_adj.mpr ⟨hxy,hxa,hya⟩,hxb,hyb⟩
    exact Or.inr (Or.inr (hux.trans hRxy.reachable))
  have hp (x : V) : 0 < G.degree x := by
    have hh := hG.degree_lower hC x
    omega
  have ha : A ≠ ⊥ := by
    obtain ⟨x,hx⟩ := (G.degree_pos_iff_exists_adj u).mp (hp u)
    have hh : A.Adj u x := ⟨hx,huS,hclosed huS hua hub hx⟩
    intro hbot
    simp only [hbot,bot_adj] at hh
  have hb : B ≠ ⊥ := by
    obtain ⟨x,hx⟩ := (G.degree_pos_iff_exists_adj w).mp (hp w)
    have hh : B.Adj w x := ⟨hx,fun h => hwS h.2.1⟩
    intro hbot
    simp only [hbot,bot_adj] at hh
  have hdis : Disjoint A.edgeSet B.edgeSet := by
    change Disjoint A.edgeSet (G \ A).edgeSet
    rw [edgeSet_sdiff]
    exact Set.disjoint_sdiff_right
  have hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet := by
    change A.edgeSet ∪ (G \ A).edgeSet = G.edgeSet
    rw [edgeSet_sdiff]
    exact Set.union_diff_cancel (edgeSet_mono hA)
  have hinter : A.support ∩ B.support ⊆ {a,b} := by
    rintro x ⟨⟨y,hy⟩,⟨z,hz⟩⟩
    by_cases hxa : x = a
    · exact Or.inl hxa
    by_cases hxb : x = b
    · exact Or.inr hxb
    exact (hz.2 ⟨hz.1,hy.2.1,hclosed hy.2.1 hxa hxb hz.1⟩).elim
  have hwA : w ∉ A.support := by
    rintro ⟨x,hx⟩
    exact hwS hx.2.1
  have huB : u ∉ B.support := by
    rintro ⟨x,hx⟩
    exact hx.2 ⟨hx.1,huS,hclosed huS hua hub hx.1⟩
  have hAl : A.support.ncard < Fintype.card V := by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
      using Fintype.card_subtype_lt hwA
  have hBl : B.support.ncard < Fintype.card V := by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
      using Fintype.card_subtype_lt huB
  exact hG.no_two_vertex_split A B hab hA hB hdis hcover hinter
    (support_card_two_le A ha) (support_card_two_le B hb) hAl hBl

end Erdos184.ShiftedCritical
