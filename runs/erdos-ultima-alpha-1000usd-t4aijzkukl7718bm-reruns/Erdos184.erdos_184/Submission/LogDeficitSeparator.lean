import Submission.LogDeficit
import Submission.SqrtDeficitResilience

/-! A logarithmic-deficit normalization and its resilient separator bounds.
These are necessary conditions for a counterexample, not their exclusion. -/
open SimpleGraph Filter
open scoped Classical
namespace Erdos184.LogDeficitSeparator
open ExactVertexSmoothing LogDeficit
universe u
set_option maxHeartbeats 1000000

def HasBound {V : Type*} [Fintype V] (C : ℕ) (G : SimpleGraph V) : Prop :=
  HasPieceBound (budget C (Fintype.card V)) G

lemma hasBound_bot {V : Type*} [Fintype V] (C : ℕ) :
    HasBound C (⊥ : SimpleGraph V) :=
  ⟨∅,by simp,by simp [IsDecomposition],by simp⟩

/-- The single infinite profile is uniformly between n and 2n. No truncation
parameter or graph-dependent rescaling of C is used. -/
theorem conjecture_iff_log_deficit_bound :
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
    refine ⟨N,?_⟩
    intro V _ G he
    obtain ⟨D,hD,hd,hcard⟩ := hc G he
    refine ⟨D,hD,hd,?_⟩
    have hb : (D.card : ℝ) ≤ ((N * Fintype.card V : ℕ) : ℝ) := by
      calc
        _ ≤ c * Fintype.card V := hcard
        _ ≤ (N : ℝ)*Fintype.card V :=
          mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg _)
        _ = _ := by push_cast; rfl
    exact (show D.card ≤ N * Fintype.card V by exact_mod_cast hb).trans (mul_le_budget _ _)
  · rintro ⟨C,hC⟩
    refine ⟨2*C,?_⟩
    intro V _ _ G he
    obtain ⟨D,hD,hd,hcard⟩ := hC G he
    refine ⟨D,hD,hd,?_⟩
    have hb := hcard.trans (budget_le C (Fintype.card V))
    exact_mod_cast hb

/-- Minimal order among counterexamples to this particular charge. -/
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

variable {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}

lemma IsVertexMinimal.bound_on_smaller_support
    (hG : IsVertexMinimal C G) (A : SimpleGraph V)
    (hlt : A.support.ncard < Fintype.card V) (he : ∀ x, Even (A.degree x)) :
    HasPieceBound (budget C A.support.ncard) A := by
  apply ShiftedCritical.pieceBound_of_induce_support
  have hc : Fintype.card A.support = A.support.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have h := hG.2.2 (A.induce A.support) (by simpa only [hc] using hlt)
    (GlobalVertexMinimal.even_induce_support A he)
  simpa only [HasBound,hc] using h

lemma IsVertexMinimal.bound_on_support_subset
    (hG : IsVertexMinimal C G) (A : SimpleGraph V) (S : Set V)
    (hs : A.support ⊆ S) (hlt : S.ncard < Fintype.card V)
    (he : ∀ x, Even (A.degree x)) :
    HasPieceBound (budget C S.ncard) A := by
  have hc := Set.ncard_le_ncard hs
  obtain ⟨D,hD,hd,hb⟩ := hG.bound_on_smaller_support A (hc.trans_lt hlt) he
  exact ⟨D,hD,hd,hb.trans (budget_mono C hc)⟩

lemma IsVertexMinimal.support_eq_univ (hG : IsVertexMinimal C G) :
    G.support = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro v
  by_contra hv
  have hlt : G.support.ncard < Fintype.card V := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using
      Fintype.card_subtype_lt hv
  obtain ⟨D,hD,hd,hb⟩ := hG.bound_on_smaller_support G hlt hG.1
  exact hG.2.1 ⟨D,hD,hd,hb.trans
    (budget_mono C hlt.le)⟩

/-- The real charge has slope at least one; its floor budget therefore
increases by at least C at each vertex. -/
lemma IsVertexMinimal.degree_lower (hG : IsVertexMinimal C G) (hC : 0 < C)
    (v : V) : 2 * (C+2) ≤ G.degree v := by
  have hcard : Fintype.card V = Fintype.card (VertexSmoothing.Without v) + 1 := by
    rw [← Fintype.card_option]
    exact Fintype.card_congr (Equiv.optionSubtypeNe v).symm
  let B := budget C (Fintype.card (VertexSmoothing.Without v))
  have hsmall : ∀ H : SimpleGraph (VertexSmoothing.Without v),
      (∀ x, Even (H.degree x)) → HasPieceBound B H := by
    intro H heH
    exact hG.2.2 H (Fintype.card_subtype_lt (x := v) (by simp)) heH
  have hBC : B + C ≤ budget C (Fintype.card V) := by
    rw [hcard]
    exact budget_succ C (Fintype.card (VertexSmoothing.Without v))
  have hbad (D : Finset G.Subgraph)
      (hc : ∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
      (hd : IsDecomposition G D) : B + C < D.card := by
    by_contra! h
    exact hG.2.1 ⟨D,hc,hd,h.trans hBC⟩
  by_cases hfour : 4 ≤ G.degree v
  · obtain ⟨D,hc,hd,hb⟩ := CliqueSmoothing.general_exact_cost B G hG.1 v hfour hsmall
    have hbadD := hbad D hc hd
    obtain ⟨r,hr⟩ := hG.1 v
    omega
  · obtain ⟨D,hc,hd,hb⟩ := unconditional_exact_cost B G hG.1 v hsmall
    have hbadD := hbad D hc hd
    omega


/-- A separator bound for any even remainder that can be completed at cost p.
The remainder is NOT assumed to be a minimal counterexample. -/
lemma IsVertexMinimal.separator_bound_of_completion (hG : IsVertexMinimal C G)
    (hC : 0 < C) (R : SimpleGraph V) (heR : ∀ v, Even (R.degree v)) (p t : ℕ)
    (hp : p ≤ C*t)
    (hcomplete : ∀ k, HasPieceBound k R → HasPieceBound (k+p) G)
    (U W : Set V) (hUW : U ∪ W = Set.univ)
    (hUl : U.ncard < Fintype.card V) (hWl : W.ncard < Fintype.card V)
    (hcross : ∀ x ∈ U \ W, ∀ y ∈ W \ U, ¬R.Adj x y)
    (j : ℕ) (hjU : 2^j ≤ U.ncard) (hjW : 2^j ≤ W.ncard) :
    (2^j : ℕ)*weight j < (3 * (U ∩ W).ncard + t : ℕ) := by
  by_contra! hs
  let A := RankBlocks.sideGraph R U
  let B := R \ A
  have hA : A ≤ R := fun _ _ h => h.1
  have hB : B ≤ R := sdiff_le
  have hd : Disjoint A.edgeSet B.edgeSet := by
    change Disjoint A.edgeSet (R \ A).edgeSet
    rw [edgeSet_sdiff]
    exact Set.disjoint_sdiff_right
  have hu : A.edgeSet ∪ B.edgeSet = R.edgeSet := by
    change A.edgeSet ∪ (R \ A).edgeSet = R.edgeSet
    rw [edgeSet_sdiff]
    exact Set.union_diff_cancel (edgeSet_mono hA)
  have hAU : A.support ⊆ U := by
    rintro x ⟨y,hxy⟩
    exact hxy.2.1
  have hmem (x : V) : x ∈ U ∨ x ∈ W := by
    have hx : x ∈ (Set.univ : Set V) := Set.mem_univ _
    rwa [← hUW] at hx
  have hBW : B.support ⊆ W := by
    rintro x ⟨y,hxy⟩
    by_contra hxW
    have hxU : x ∈ U := (hmem x).resolve_right hxW
    have hyU : y ∈ U := by
      by_contra hyU
      exact hcross x ⟨hxU,hxW⟩ y ⟨(hmem y).resolve_left hyU,hyU⟩ hxy.1
    exact hxy.2 ⟨hxy.1,hxU,hyU⟩
  have hn := Set.ncard_union_add_ncard_inter U W
  rw [hUW,Set.ncard_univ,Nat.card_eq_fintype_card] at hn
  have hb := separator_budget hC
    (by omega : Fintype.card V ≤ U.ncard + W.ncard)
    (by omega : U.ncard + W.ncard ≤ Fintype.card V + (U ∩ W).ncard) hp hjU hjW hs
  have hR := ForestBoundaryBudget.decomposition_of_finite_separation
    (U ∩ W) heR hA hB hd hu
    (fun _ hx => ⟨hAU hx.1,hBW hx.2⟩)
    (budget C U.ncard) (budget C W.ncard)
    (fun X hX he => hG.bound_on_support_subset X U
      ((support_mono hX).trans hAU) hUl he)
    (fun X hX he => hG.bound_on_support_subset X W
      ((support_mono hX).trans hBW) hWl he)
  obtain ⟨D,hD,hdec,hcard⟩ := hcomplete _ hR
  exact hG.2.1 ⟨D,hD,hdec,hcard.trans hb⟩

/-- Removing a bounded number of whole cycles gives a controlled separator
loss, quantified by t rather than silently retaining the original bound. -/
lemma IsVertexMinimal.packing_separator_bound (hG : IsVertexMinimal C G)
    (hC : 0 < C) (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (t : ℕ) (hp : P.card ≤ C*t)
    (U W : Set V) (hUW : U ∪ W = Set.univ)
    (hUl : U.ncard < Fintype.card V) (hWl : W.ncard < Fintype.card V)
    (hcross : ∀ x ∈ U \ W, ∀ y ∈ W \ U, ¬(G \ unionPieces G P).Adj x y)
    (j : ℕ) (hjU : 2^j ≤ U.ncard) (hjW : 2^j ≤ W.ncard) :
    (2^j : ℕ)*weight j < (3 * (U ∩ W).ncard + t : ℕ) := by
  apply hG.separator_bound_of_completion hC (G \ unionPieces G P) _ P.card t hp
    (SqrtDeficitSeparator.completion_of_packing G P hc hd) U W hUW hUl hWl hcross j hjU hjW
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    using even_residual_of_cycle_packing G hG.1 P hc hd v

/-- Arbitrary edge deletion is handled by covering the deleted edges with
at most as many pieces of one genuine cycle decomposition. G-F need not be even. -/
lemma IsVertexMinimal.edge_deletion_separator_bound (hG : IsVertexMinimal C G)
    (hC : 0 < C) (F : Set (Sym2 V)) (t : ℕ) (hF : F.ncard ≤ C*t)
    (U W : Set V) (hUW : U ∪ W = Set.univ)
    (hUl : U.ncard < Fintype.card V) (hWl : W.ncard < Fintype.card V)
    (hcross : ∀ x ∈ U \ W, ∀ y ∈ W \ U, ¬(G.deleteEdges F).Adj x y)
    (j : ℕ) (hjU : 2^j ≤ U.ncard) (hjW : 2^j ≤ W.ncard) :
    (2^j : ℕ)*weight j < (3 * (U ∩ W).ncard + t : ℕ) := by
  obtain ⟨D,hc,hd⟩ := even_cycle_decomposition G hG.1
  obtain ⟨P,hPD,hPF,hres⟩ := ShiftedCritical.exists_packing_cover_edges D hd F
  exact hG.packing_separator_bound hC P
    (fun H hH => hc H (hPD hH))
    (fun H hH K hK hne => hd.1 (hPD hH) (hPD hK) hne)
    t (hPF.trans hF) U W hUW hUl hWl
    (fun x hx y hy hxy => hcross x hx y hy (hres hxy)) j hjU hjW


end Erdos184.LogDeficitSeparator
