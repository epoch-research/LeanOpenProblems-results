import Submission.FourVertexSeparation
import Submission.FiniteSeparatorExtraction

/-!
The equivalent positive-part C(n-5) normalization and its vertex-minimal
counterexamples. This is a structural reduction, not a uniform bound.
-/
open SimpleGraph Filter
open scoped Classical
namespace Erdos184.ShiftFiveCritical
open ExactVertexSmoothing
universe u

def charge (n : ℕ) : ℕ := max (n-5) 1

def HasBound {V : Type*} [Fintype V] (C : ℕ) (G : SimpleGraph V) : Prop :=
  HasPieceBound (C * charge (Fintype.card V)) G

lemma hasBound_bot {V : Type*} [Fintype V] (C : ℕ) :
    HasBound C (⊥ : SimpleGraph V) :=
  ⟨∅,by simp,by simp [IsDecomposition],by simp⟩

/-- The small-order exception does not change the asymptotic conjecture. -/
theorem conjecture_iff_shift_five_bound :
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
    refine ⟨6*N,?_⟩
    intro V _ G he
    obtain ⟨D,hD,hd,hcard⟩ := hc G he
    refine ⟨D,hD,hd,?_⟩
    have hn : Fintype.card V ≤ 6 * charge (Fintype.card V) := by unfold charge; omega
    have hb : (D.card : ℝ) ≤ ((6*N) * charge (Fintype.card V) : ℕ) := by
      calc
        (D.card : ℝ) ≤ c * Fintype.card V := hcard
        _ ≤ (N : ℝ) * Fintype.card V := mul_le_mul_of_nonneg_right hN (by positivity)
        _ ≤ (N : ℝ) * (6 * charge (Fintype.card V) : ℕ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact_mod_cast hn
        _ = _ := by push_cast; ring
    exact_mod_cast hb
  · rintro ⟨C,hC⟩
    refine ⟨C,?_⟩
    intro V _ _ G he
    by_cases hb : G = ⊥
    · subst G
      exact ⟨∅,by simp,by simp [IsDecomposition],by simp only [Finset.card_empty,Nat.cast_zero]; positivity⟩
    have hn := ShiftedCritical.three_le_card_of_even_ne_bot G he hb
    obtain ⟨D,hD,hd,hcard⟩ := hC G he
    have hcharge : charge (Fintype.card V) ≤ Fintype.card V := by unfold charge; omega
    exact ⟨D,hD,hd,by exact_mod_cast hcard.trans (Nat.mul_le_mul_left C hcharge)⟩

/-- Minimal order, with arbitrary changes of edges allowed at smaller order. -/
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

/-- First minimize order, then edge count. -/
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

lemma bound_of_small_order {V : Type*} [Fintype V] {C : ℕ} (hC : 15 ≤ C)
    (G : SimpleGraph V) (he : ∀ v, Even (G.degree v)) (hn : Fintype.card V ≤ 6) :
    HasBound C G := by
  obtain ⟨D,hD,hd,hcard⟩ := quadratic_decomposition G
  obtain ⟨E,hE,heE,hED⟩ := refine_even_decomposition G he D hD hd
  have hchoose : (Fintype.card V).choose 2 ≤ 15 := by
    exact (Nat.choose_le_choose 2 hn).trans (by decide)
  have hone : 1 ≤ charge (Fintype.card V) := le_max_right _ _
  have hmul : C ≤ C * charge (Fintype.card V) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left C hone
  exact ⟨E,hE,heE,by omega⟩

lemma IsVertexMinimal.order_lower {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsVertexMinimal C G) (hC : 15 ≤ C) : 7 ≤ Fintype.card V := by
  by_contra! hn
  exact hG.2.1 (bound_of_small_order hC G hG.1 (by omega))

lemma IsVertexMinimal.degree_lower {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsVertexMinimal C G) (hC : 15 ≤ C) (v : V) : 2 * (C+2) ≤ G.degree v := by
  have hn := hG.order_lower hC
  have hcard : Fintype.card V = Fintype.card (VertexSmoothing.Without v) + 1 := by
    rw [← Fintype.card_option]
    exact Fintype.card_congr (Equiv.optionSubtypeNe v).symm
  let B := C * charge (Fintype.card (VertexSmoothing.Without v))
  have hsmall : ∀ H : SimpleGraph (VertexSmoothing.Without v),
      (∀ x, Even (H.degree x)) → HasPieceBound B H := by
    intro H heH
    exact hG.2.2 H (Fintype.card_subtype_lt (x := v) (by simp)) heH
  have hBC : B + C = C * charge (Fintype.card V) := by
    change C * charge (Fintype.card (VertexSmoothing.Without v)) + C = _
    calc
      _ = C * (charge (Fintype.card (VertexSmoothing.Without v)) + 1) := by ring
      _ = _ := by congr 1; unfold charge; omega
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

lemma IsVertexMinimal.bound_on_smaller_support {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (A : SimpleGraph V)
    (hlt : A.support.ncard < Fintype.card V) (he : ∀ x, Even (A.degree x)) :
    HasPieceBound (C * charge A.support.ncard) A := by
  apply ShiftedCritical.pieceBound_of_induce_support
  have hc : Fintype.card A.support = A.support.ncard := by
    rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have h := hG.2.2 (A.induce A.support) (by simpa only [hc] using hlt)
    (GlobalVertexMinimal.even_induce_support A he)
  simpa only [HasBound,hc] using h

lemma IsVertexMinimal.bound_on_support_subset {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (A : SimpleGraph V) (S : Set V)
    (hs : A.support ⊆ S) (hlt : S.ncard < Fintype.card V)
    (he : ∀ x, Even (A.degree x)) : HasPieceBound (C * charge S.ncard) A := by
  have hcard := Set.ncard_le_ncard hs
  obtain ⟨D,hc,hd,hb⟩ := hG.bound_on_smaller_support A (hcard.trans_lt hlt) he
  have hcharge : charge A.support.ncard ≤ charge S.ncard := by unfold charge; omega
  exact ⟨D,hc,hd,hb.trans (Nat.mul_le_mul_left C hcharge)⟩

/-- Four-terminal separator gluing contradicts minimality when both side supports
are proper and have at least six vertices. -/
lemma IsVertexMinimal.no_four_vertex_split {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 4 ≤ C)
    (A B : SimpleGraph V) (S : Set V) (hS : S.ncard ≤ 4)
    (hA : A ≤ G) (hB : B ≤ G)
    (hdis : Disjoint A.edgeSet B.edgeSet) (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hinter : A.support ∩ B.support ⊆ S)
    (hAc : 6 ≤ A.support.ncard) (hBc : 6 ≤ B.support.ncard)
    (hAl : A.support.ncard < Fintype.card V) (hBl : B.support.ncard < Fintype.card V) : False := by
  obtain ⟨D,hc,hd,hb⟩ := FiniteTerminalGluing.decomposition_of_four_separation S hS hG.1 hA hB
    hdis hcover hinter (C * charge A.support.ncard) (C * charge B.support.ncard)
    (fun X hs he => hG.bound_on_support_subset X A.support hs hAl he)
    (fun Y hs he => hG.bound_on_support_subset Y B.support hs hBl he)
  have hover := (Set.ncard_le_ncard hinter).trans hS
  have hsum := Set.ncard_union_add_ncard_inter A.support B.support
  rw [support_union_of_edge_cover hcover] at hsum
  have hs : G.support.ncard ≤ Fintype.card V := by
    simpa using Set.ncard_le_ncard (Set.subset_univ G.support)
  have hcharge : charge A.support.ncard + charge B.support.ncard + 1 ≤ charge (Fintype.card V) := by
    unfold charge
    omega
  have hbudget := Nat.mul_le_mul_left C hcharge
  simp only [Nat.mul_add,Nat.mul_one] at hbudget
  exact hG.2.1 ⟨D,hc,hd,by omega⟩

/-- Every specified cycle has an optimum extension, with the exact shifted value. -/
lemma IsLexMinimal.extend_cycle {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}
    (hG : IsLexMinimal C G) (H : G.Subgraph)
    (hH : H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) :
    ∃ D : Finset G.Subgraph,
      (∀ K ∈ D, K.coe.Connected ∧ K.coe.IsRegularOfDegree 2) ∧
      IsDecomposition G D ∧ H ∈ D ∧ D.card = C * charge (Fintype.card V) + 1 := by
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
  have hbad : C * charge (Fintype.card V) < D.card := by
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
  have hbad : C * charge (Fintype.card V) < E.card := by
    by_contra! h
    exact hG.1.2.1 ⟨E,hE,he,h⟩
  omega

set_option maxHeartbeats 800000 in
/-- A vertex-minimal counterexample is five-vertex-connected: deleting any
set of at most four vertices preserves reachability between all others. -/
lemma IsVertexMinimal.induce_compl_reachable {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 15 ≤ C)
    (S : Set V) (hS : S.ncard ≤ 4) (u w : ↥(Sᶜ)) :
    (G.induce Sᶜ).Reachable u w := by
  apply FiniteTerminalGluing.induce_compl_reachable_of_no_split G S 6
  · intro x
    have hh := hG.degree_lower hC x
    omega
  · intro A B hA hB hd hu hv hAc hBc hAl hBl
    exact hG.no_four_vertex_split (by omega) A B S hS hA hB hd hu hv hAc hBc hAl hBl

lemma IsVertexMinimal.connected {V : Type u} [Fintype V]
    {C : ℕ} {G : SimpleGraph V} (hG : IsVertexMinimal C G) (hC : 15 ≤ C) : G.Connected := by
  have hn := hG.order_lower hC
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  refine { preconnected := ?_, nonempty := inferInstance }
  intro a b
  have hh := hG.induce_compl_reachable hC ∅ (by simp)
    (⟨a,by simp⟩ : ↥((∅ : Set V)ᶜ)) (⟨b,by simp⟩ : ↥((∅ : Set V)ᶜ))
  exact hh.map (SimpleGraph.Embedding.induce ((∅ : Set V)ᶜ)).toHom

end Erdos184.ShiftFiveCritical
