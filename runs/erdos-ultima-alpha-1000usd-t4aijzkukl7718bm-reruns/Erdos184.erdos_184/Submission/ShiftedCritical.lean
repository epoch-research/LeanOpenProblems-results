import Submission.RankBlocks

/-!
The equivalent `C * (n-2)` normalization.  Its extra slack is useful for
vertex sums, but no uniform constant is proved here.
-/
open SimpleGraph Filter
open scoped Classical
namespace Erdos184.ShiftedCritical
open ExactVertexSmoothing
universe u

/-- Natural subtraction handles the empty graphs of orders zero, one, and two. -/
def HasBound {V : Type*} [Fintype V] (C : ℕ) (G : SimpleGraph V) : Prop :=
  HasPieceBound (C * (Fintype.card V - 2)) G

lemma hasBound_bot {V : Type*} [Fintype V] (C : ℕ) :
    HasBound C (⊥ : SimpleGraph V) :=
  ⟨∅, by simp, by simp [IsDecomposition], by simp⟩

lemma three_le_card_of_even_ne_bot {V : Type*} [Fintype V] (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hne : G ≠ ⊥) : 3 ≤ Fintype.card V := by
  obtain ⟨a,b,hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  have hp := G.degree_pos_iff_mem_support a |>.mpr ⟨b,hab⟩
  obtain ⟨k,hk⟩ := he a
  have hd := G.degree_lt_card_verts a
  omega

/-- Changing the intercept does not change the original asymptotic conjecture. -/
theorem conjecture_iff_shifted_bound :
    (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      ∃ D : Finset G.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ f (Fintype.card V)) ↔
    (∃ C : ℕ, ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) → HasBound C G) := by
  rw [conjecture_iff_even_cycle_bound]
  constructor
  · rintro ⟨c,hc⟩
    obtain ⟨N,hN⟩ := exists_nat_ge c
    refine ⟨3*N,?_⟩
    intro V _ G he
    by_cases hb : G = ⊥
    · subst G
      exact hasBound_bot _
    have hn := three_le_card_of_even_ne_bot G he hb
    obtain ⟨D,hD,hd,hcard⟩ := hc G he
    refine ⟨D,hD,hd,?_⟩
    have hn' : Fintype.card V ≤ 3 * (Fintype.card V - 2) := by omega
    have hbound : (D.card : ℝ) ≤ ((3*N) * (Fintype.card V - 2) : ℕ) := by
      calc
        (D.card : ℝ) ≤ c * Fintype.card V := hcard
        _ ≤ (N : ℝ) * Fintype.card V :=
          mul_le_mul_of_nonneg_right hN (by positivity)
        _ ≤ (N : ℝ) * (3 * (Fintype.card V - 2 : ℕ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact_mod_cast hn'
        _ = _ := by push_cast; ring
    exact_mod_cast hbound
  · rintro ⟨C,hC⟩
    refine ⟨C,?_⟩
    intro V _ _ G he
    obtain ⟨D,hD,hd,hcard⟩ := hC G he
    exact ⟨D,hD,hd,by exact_mod_cast
      (hcard.trans (Nat.mul_le_mul_left C (Nat.sub_le (Fintype.card V) 2)))⟩

/-- Minimal order among all even simple graphs failing the shifted bound. -/
def IsVertexMinimal {V : Type u} [Fintype V] (C : ℕ) (G : SimpleGraph V) : Prop :=
  (∀ v, Even (G.degree v)) ∧ ¬HasBound C G ∧
  ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
    Fintype.card W < Fintype.card V →
    (∀ w, Even (H.degree w)) → HasBound C H

lemma exists_vertex_minimal {V : Type u} [Fintype V] (C : ℕ) (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hb : ¬HasBound C G) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W), IsVertexMinimal C H := by
  let P (n : ℕ) := ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
    (∀ w, Even (H.degree w)) ∧ ¬HasBound C H ∧ Fintype.card W = n
  have hex : ∃ n, P n := ⟨_,V,inferInstance,G,he,hb,rfl⟩
  obtain ⟨W,instW,H,heH,hbH,hn⟩ := Nat.find_spec hex
  letI := instW
  refine ⟨W,instW,H,heH,hbH,?_⟩
  intro X instX A hlt heA
  by_contra hbA
  have hh := Nat.find_min' hex
    (show P (Fintype.card X) from ⟨X,instX,A,heA,hbA,rfl⟩)
  omega

/-- First minimize order, then minimize edge count, allowing arbitrary new edges. -/
def IsLexMinimal {V : Type u} [Fintype V] (C : ℕ) (G : SimpleGraph V) : Prop :=
  IsVertexMinimal C G ∧
  ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
    Fintype.card W = Fintype.card V → H.edgeSet.ncard < G.edgeSet.ncard →
    (∀ w, Even (H.degree w)) → HasBound C H

lemma exists_lex_minimal {V : Type u} [Fintype V] (C : ℕ) (G : SimpleGraph V)
    (he : ∀ v, Even (G.degree v)) (hb : ¬HasBound C G) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W), IsLexMinimal C H := by
  obtain ⟨X,instX,A,hA⟩ := exists_vertex_minimal C G he hb
  letI := instX
  let P (m : ℕ) := ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
    (∀ w, Even (H.degree w)) ∧ ¬HasBound C H ∧
    Fintype.card W = Fintype.card X ∧ H.edgeSet.ncard = m
  have hex : ∃ m, P m := ⟨_,X,instX,A,hA.1,hA.2.1,rfl,rfl⟩
  obtain ⟨W,instW,H,heH,hbH,hn,hm⟩ := Nat.find_spec hex
  letI := instW
  refine ⟨W,instW,H,⟨heH,hbH,?_⟩,?_⟩
  · intro Y instY K hlt heK
    exact hA.2.2 K (by omega) heK
  · intro Y instY K hcard hlt heK
    by_contra hbK
    have hmin := Nat.find_min' hex
      (show P K.edgeSet.ncard from ⟨Y,instY,K,heK,hbK,hcard.trans hn,rfl⟩)
    omega

lemma IsVertexMinimal.ne_bot {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsVertexMinimal C G) : G ≠ ⊥ := by
  intro h
  exact hG.2.1 (h ▸ hasBound_bot C)

/-- The existing exact smoothing bound still gives the same strong degree gap. -/
lemma IsVertexMinimal.degree_lower {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsVertexMinimal C G) (hC : 0 < C) (v : V) : 2 * (C+2) ≤ G.degree v := by
  have hn := three_le_card_of_even_ne_bot G hG.1 hG.ne_bot
  have hcard : Fintype.card V = Fintype.card (VertexSmoothing.Without v) + 1 := by
    rw [← Fintype.card_option]
    exact Fintype.card_congr (Equiv.optionSubtypeNe v).symm
  let B := C * (Fintype.card (VertexSmoothing.Without v) - 2)
  have hsmall : ∀ H : SimpleGraph (VertexSmoothing.Without v),
      (∀ x, Even (H.degree x)) → HasPieceBound B H := by
    intro H heH
    exact hG.2.2 H (Fintype.card_subtype_lt (x := v) (by simp)) heH
  have hBC : B + C = C * (Fintype.card V - 2) := by
    change C * (Fintype.card (VertexSmoothing.Without v) - 2) + C = _
    calc
      _ = C * ((Fintype.card (VertexSmoothing.Without v) - 2) + 1) := by ring
      _ = _ := by congr 1; omega
  have hbad (D : Finset G.Subgraph)
      (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
      (hd : IsDecomposition G D) : B + C < D.card := by
    rw [hBC]
    by_contra! h
    exact hG.2.1 ⟨D,hc,hd,h⟩
  by_cases hfour : 4 ≤ G.degree v
  · obtain ⟨D,hc,hd,hb⟩ := CliqueSmoothing.general_exact_cost B G hG.1 v hfour hsmall
    have hbadD := hbad D hc hd
    obtain ⟨r,hr⟩ := hG.1 v
    omega
  · obtain ⟨D,hc,hd,hb⟩ := unconditional_exact_cost B G hG.1 v hsmall
    have hbadD := hbad D hc hd
    omega

/-- Every specified cycle has an optimum extension, with the exact shifted value. -/
lemma IsLexMinimal.extend_cycle {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsLexMinimal C G) (H : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    ∃ D : Finset G.Subgraph,
      (∀ K ∈ D, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ H ∈ D ∧ D.card = C * (Fintype.card V - 2) + 1 := by
  let P : Finset G.Subgraph := {H}
  have hc : ∀ K ∈ P, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2 := by
    intro K hK
    obtain rfl := Finset.mem_singleton.mp hK
    exact hH
  have hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun K => K.edgeSet) := by simp [P]
  have heR := even_residual_of_cycle_packing G hG.1.1 P hc hd
  obtain ⟨F,hcF,hdF,hbF⟩ := hG.2 (G \ unionPieces G P) rfl
    (MinimalCounterexample.residual_edge_card_lt G P (Finset.singleton_nonempty _) hc) (by
      intro w
      simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using heR w)
  obtain ⟨D,hcD,hdD,hPD,hbD⟩ := complete_cycle_packing_extension G P hc hd F (by
    intro K hK
    refine ⟨(hcF K hK).1,?_⟩
    intro w
    simpa only [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] using (hcF K hK).2 w) hdF
  have hbad : C * (Fintype.card V - 2) < D.card := by
    by_contra! h
    exact hG.1.2.1 ⟨D,hcD,hdD,h⟩
  have hP : P.card = 1 := Finset.card_singleton _
  exact ⟨D,hcD,hdD,hPD (Finset.mem_singleton_self H),by omega⟩

lemma IsLexMinimal.allCyclesOptimal {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsLexMinimal C G) : MinimalCounterexample.AllCyclesOptimal G := by
  intro H hH
  obtain ⟨D,hD,hd,hHD,hn⟩ := hG.extend_cycle H hH
  refine ⟨D,hD,hd,hHD,?_⟩
  intro E hE he
  have hbad : C * (Fintype.card V - 2) < E.card := by
    by_contra! h
    exact hG.1.2.1 ⟨E,hE,he,h⟩
  omega

lemma sum_sub_two_le {I : Type*} (s : Finset I) (f : I → ℕ) :
    (∑ i ∈ s, (f i - 2)) ≤ (∑ i ∈ s, f i) - 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    omega

lemma bound_of_component_bounds {V : Type*} [Fintype V] (C : ℕ) (G : SimpleGraph V)
    (hb : ∀ c : G.ConnectedComponent, HasBound C c.toSimpleGraph) : HasBound C G := by
  choose D hc hd hcard using hb
  obtain ⟨E,hcE,hdE,hcardE⟩ := RankComponents.combine_component_decompositions G D hc hd
  refine ⟨E,hcE,hdE,hcardE.trans ?_⟩
  have hh : (∑ c, (D c).card) ≤ ∑ c : G.ConnectedComponent, C * (Fintype.card c - 2) := by
    exact Finset.sum_le_sum (fun c _ => hcard c)
  rw [← Finset.mul_sum] at hh
  apply hh.trans
  apply Nat.mul_le_mul_left
  rw [RankComponents.card_eq_sum_component_card G]
  exact sum_sub_two_le _ _

lemma IsVertexMinimal.connected {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsVertexMinimal C G) : G.Connected := by
  by_contra hn
  apply hG.2.1
  apply bound_of_component_bounds
  intro c
  have hex : ∃ v : V, v ∉ c.supp := by
    by_contra! hh
    apply hn
    exact c.connected_toSimpleGraph.map c.toSimpleGraph_hom
      (fun v => ⟨⟨v,hh v⟩,rfl⟩)
  obtain ⟨v,hv⟩ := hex
  apply hG.2.2 c.toSimpleGraph
  · simpa only [← Nat.card_eq_fintype_card] using Fintype.card_subtype_lt hv
  · intro x
    have hx := hG.1 x.val
    have hd := component_degree G c x
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hx hd ⊢
    rwa [hd]

lemma pieceBound_of_induce_support {V : Type*} [Fintype V] (G : SimpleGraph V) {B : ℕ}
    (hb : HasPieceBound B (G.induce G.support)) : HasPieceBound B G := by
  let f : G.induce G.support →g G := (SimpleGraph.Embedding.induce G.support).toHom
  have hi : Set.InjOn (Sym2.map f) (G.induce G.support).edgeSet :=
    (Sym2.map.injective Subtype.val_injective).injOn
  have hs : Set.SurjOn (Sym2.map f) (G.induce G.support).edgeSet G.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h x y => exact ⟨s(⟨x,⟨y,he⟩⟩,⟨y,⟨x,he.symm⟩⟩),he,rfl⟩
  obtain ⟨D,hc,hd,hbD⟩ := hb
  obtain ⟨E,hcE,hdE,hbE⟩ := project_decomposition_degree_two f hi hs ∅
    Subtype.val_injective.injOn (by simp) D (by
      intro H hH
      refine ⟨(hc H hH).1,?_⟩
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using (hc H hH).2 v) hd
  refine ⟨E,hcE,hdE,?_⟩
  have hbE' : E.card ≤ D.card := by simpa using hbE
  exact hbE'.trans hbD

lemma IsVertexMinimal.bound_on_smaller_support {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (A : SimpleGraph V)
    (hlt : A.support.ncard < Fintype.card V) (he : ∀ x, Even (A.degree x)) :
    HasPieceBound (C * (A.support.ncard - 2)) A := by
  apply pieceBound_of_induce_support
  have hc : Fintype.card A.support = A.support.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have h := hG.2.2 (A.induce A.support) (by simpa only [hc] using hlt)
    (GlobalVertexMinimal.even_induce_support A he)
  simpa only [HasBound,hc] using h

lemma IsVertexMinimal.no_one_vertex_split {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) : ¬HasEvenOneVertexSplit G := by
  rintro ⟨A,B,hA,hB,ha,hb,hea,heb,hab,hcover,hover⟩
  have hAc := support_card_two_le A ha
  have hBc := support_card_two_le B hb
  have hsum := Set.ncard_union_add_ncard_inter A.support B.support
  rw [support_union_of_edge_cover hcover] at hsum
  have hs : G.support.ncard ≤ Fintype.card V := by
    simpa using Set.ncard_le_ncard (Set.subset_univ G.support)
  obtain ⟨DA,hca,hda,hba⟩ := hG.bound_on_smaller_support A (by omega) hea
  obtain ⟨DB,hcb,hdb,hbb⟩ := hG.bound_on_smaller_support B (by omega) heb
  obtain ⟨D,hdcy,hdd,hbd⟩ := combine_decompositions hA hB hab hcover DA DB
    (fun H hH => Or.inl ⟨(hca H hH).1,by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hca H hH).2 v⟩)
    (fun H hH => Or.inl ⟨(hcb H hH).1,by
      intro v
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] using (hcb H hH).2 v⟩)
    hda hdb
  obtain ⟨E,hce,hde,hbe⟩ := refine_even_decomposition G hG.1 D hdcy hdd
  apply hG.2.1
  refine ⟨E,hce,hde,?_⟩
  have hh := Nat.mul_le_mul_left C (show
    (A.support.ncard - 2) + (B.support.ncard - 2) ≤ Fintype.card V - 2 by omega)
  rw [Nat.mul_add] at hh
  omega

lemma IsVertexMinimal.delete_vertex_reachable {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G)
    {v a b : V} (ha : a ≠ v) (hb : b ≠ v) :
    (G.deleteIncidenceSet v).Reachable a b := by
  by_contra hn
  exact hG.no_one_vertex_split
    (RankBlocks.split_of_deleted_unreachable hG.connected hG.1 ha hb hn)

end Erdos184.ShiftedCritical
