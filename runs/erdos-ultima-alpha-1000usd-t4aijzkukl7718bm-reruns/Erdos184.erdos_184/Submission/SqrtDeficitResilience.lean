import Submission.SqrtDeficitSeparator
import Submission.ShiftedPackingConnectivity

/-! Quantified resilience of the square-root separator restriction.
These are necessary conditions on counterexamples, not their exclusion. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.SqrtDeficitSeparator
open ExactVertexSmoothing
universe u
set_option maxHeartbeats 1000000

lemma separator_budget_with_cost {C a b n s p t : ℕ} (hC : 0 < C)
    (hlo : n ≤ a+b) (hhi : a+b ≤ n+s) (hp : p ≤ C*t)
    (hs : 6*s+2*t+4 ≤ Nat.sqrt (min a b)) :
    C * deficit a + C * deficit b + (s-1) + p ≤ C * deficit n := by
  have hg : 2 * Nat.sqrt n ≤ 2 * max (Nat.sqrt a) (Nat.sqrt b) +
      min (Nat.sqrt a) (Nat.sqrt b) + 4 := by
    rcases le_total a b with hab | hba
    · simpa only [max_eq_right (Nat.sqrt_le_sqrt hab),
        min_eq_left (Nat.sqrt_le_sqrt hab)] using sqrt_sum_gap hab hlo
    · simpa only [max_eq_left (Nat.sqrt_le_sqrt hba),
        min_eq_right (Nat.sqrt_le_sqrt hba)] using
        sqrt_sum_gap hba (by omega : n ≤ b+a)
  have hmin : Nat.sqrt (min a b) = min (Nat.sqrt a) (Nat.sqrt b) := by
    rcases le_total a b with hab | hba
    · simp [min_eq_left hab,min_eq_left (Nat.sqrt_le_sqrt hab)]
    · simp [min_eq_right hba,min_eq_right (Nat.sqrt_le_sqrt hba)]
  rw [hmin] at hs
  have hgap : Nat.sqrt n + 3*s+t ≤ Nat.sqrt a + Nat.sqrt b := by
    have hm := min_add_max (Nat.sqrt a) (Nat.sqrt b)
    omega
  have ha := Nat.sqrt_le_self a
  have hb := Nat.sqrt_le_self b
  have hn := Nat.sqrt_le_self n
  have hc : 1 ≤ C := hC
  have hdiff : deficit a + deficit b + s+t ≤ deficit n := by
    dsimp [deficit]
    omega
  have hmul := Nat.mul_le_mul_left C hdiff
  have hcs := Nat.mul_le_mul_right s hc
  have hsub := Nat.sub_le s 1
  nlinarith

variable {V : Type u} [Fintype V] {C : ℕ} {G : SimpleGraph V}

/-- A separator bound for any even remainder that can be completed at cost p.
The remainder is NOT assumed to be a minimal counterexample. -/
lemma IsVertexMinimal.separator_bound_of_completion (hG : IsVertexMinimal C G)
    (hC : 0 < C) (R : SimpleGraph V) (heR : ∀ v, Even (R.degree v)) (p t : ℕ)
    (hp : p ≤ C*t)
    (hcomplete : ∀ k, HasPieceBound k R → HasPieceBound (k+p) G)
    (U W : Set V) (hUW : U ∪ W = Set.univ)
    (hUl : U.ncard < Fintype.card V) (hWl : W.ncard < Fintype.card V)
    (hcross : ∀ x ∈ U \ W, ∀ y ∈ W \ U, ¬R.Adj x y) :
    min U.ncard W.ncard < (6 * (U ∩ W).ncard + 2*t+4)^2 := by
  by_contra! hlarge
  have hroot := Nat.le_sqrt'.mpr hlarge
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
  have hb := separator_budget_with_cost hC
    (by omega : Fintype.card V ≤ U.ncard + W.ncard)
    (by omega : U.ncard + W.ncard ≤ Fintype.card V + (U ∩ W).ncard) hp hroot
  have hR := ForestBoundaryBudget.decomposition_of_finite_separation
    (U ∩ W) heR hA hB hd hu
    (fun _ hx => ⟨hAU hx.1,hBW hx.2⟩)
    (C * deficit U.ncard) (C * deficit W.ncard)
    (fun X hX he => hG.bound_on_support_subset X U
      ((support_mono hX).trans hAU) hUl he)
    (fun X hX he => hG.bound_on_support_subset X W
      ((support_mono hX).trans hBW) hWl he)
  obtain ⟨D,hD,hdec,hcard⟩ := hcomplete _ hR
  exact hG.2.1 ⟨D,hD,hdec,hcard.trans hb⟩

lemma completion_of_packing (G : SimpleGraph V) (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (k : ℕ) (hk : HasPieceBound k (G \ unionPieces G P)) :
    HasPieceBound (k+P.card) G := by
  obtain ⟨D,hD,hdec,hcard⟩ := hk
  obtain ⟨E,hE,hdecE,hcardE⟩ := complete_cycle_packing G P hc hd D (by
    intro H hH
    refine ⟨(hD H hH).1,?_⟩
    intro v
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      using (hD H hH).2 v) hdec
  exact ⟨E,hE,hdecE,by omega⟩

/-- Removing a bounded number of whole cycles gives a controlled separator
loss, quantified by t rather than silently retaining the original bound. -/
lemma IsVertexMinimal.packing_separator_bound (hG : IsVertexMinimal C G)
    (hC : 0 < C) (P : Finset G.Subgraph)
    (hc : ∀ H ∈ P, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2)
    (hd : Set.PairwiseDisjoint (P : Set G.Subgraph) (fun H => H.edgeSet))
    (t : ℕ) (hp : P.card ≤ C*t)
    (U W : Set V) (hUW : U ∪ W = Set.univ)
    (hUl : U.ncard < Fintype.card V) (hWl : W.ncard < Fintype.card V)
    (hcross : ∀ x ∈ U \ W, ∀ y ∈ W \ U, ¬(G \ unionPieces G P).Adj x y) :
    min U.ncard W.ncard < (6 * (U ∩ W).ncard + 2*t+4)^2 := by
  apply hG.separator_bound_of_completion hC (G \ unionPieces G P) _ P.card t hp
    (completion_of_packing G P hc hd) U W hUW hUl hWl hcross
  intro v
  simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    using even_residual_of_cycle_packing G hG.1 P hc hd v

/-- Arbitrary edge deletion is handled by covering the deleted edges with
at most as many pieces of one genuine cycle decomposition. G-F need not be even. -/
lemma IsVertexMinimal.edge_deletion_separator_bound (hG : IsVertexMinimal C G)
    (hC : 0 < C) (F : Set (Sym2 V)) (t : ℕ) (hF : F.ncard ≤ C*t)
    (U W : Set V) (hUW : U ∪ W = Set.univ)
    (hUl : U.ncard < Fintype.card V) (hWl : W.ncard < Fintype.card V)
    (hcross : ∀ x ∈ U \ W, ∀ y ∈ W \ U, ¬(G.deleteEdges F).Adj x y) :
    min U.ncard W.ncard < (6 * (U ∩ W).ncard + 2*t+4)^2 := by
  obtain ⟨D,hc,hd⟩ := even_cycle_decomposition G hG.1
  obtain ⟨P,hPD,hPF,hres⟩ := ShiftedCritical.exists_packing_cover_edges D hd F
  exact hG.packing_separator_bound hC P
    (fun H hH => hc H (hPD hH))
    (fun H hH K hK hne => hd.1 (hPD hH) (hPD hK) hne)
    t (hPF.trans hF) U W hUW hUl hWl
    (fun x hx y hy hxy => hcross x hx y hy (hres hxy))

/-- Abstract passage from vertex-separator bounds to external neighborhoods. -/
lemma boundary_bound_of_separator_bounds (H : SimpleGraph V) (t : ℕ)
    (hsep : ∀ (U W : Set V), U ∪ W = Set.univ →
      U.ncard < Fintype.card V → W.ncard < Fintype.card V →
      (∀ x ∈ U \ W, ∀ y ∈ W \ U, ¬H.Adj x y) →
      min U.ncard W.ncard < (6 * (U ∩ W).ncard + 2*t+4)^2)
    (X : Set V) (hhalf : 2 * X.ncard ≤ Fintype.card V) :
    X.ncard < (6 * (externalBoundary H X).ncard + 2*t+4)^2 := by
  let S := externalBoundary H X
  have hdis : Disjoint X S := by
    apply Set.disjoint_left.mpr
    intro x hx hs
    exact hs.1 hx
  have hU : (X ∪ S).ncard = X.ncard + S.ncard := Set.ncard_union_eq hdis
  have hW : X.ncard + Xᶜ.ncard = Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card] using Set.ncard_add_ncard_compl X
  by_cases hzero : X.ncard = 0
  · rw [hzero]
    positivity
  by_cases hUl : (X ∪ S).ncard < Fintype.card V
  · have hWl : Xᶜ.ncard < Fintype.card V := by omega
    have hUW : (X ∪ S) ∪ Xᶜ = Set.univ := by
      ext x
      simp only [Set.mem_union,Set.mem_compl_iff,Set.mem_univ,iff_true]
      tauto
    have hinter : (X ∪ S) ∩ Xᶜ = S := by
      ext x
      have hs : x ∈ S → x ∉ X := fun h => h.1
      simp only [Set.mem_inter_iff,Set.mem_union,Set.mem_compl_iff]
      tauto
    have hc : ∀ x ∈ (X ∪ S) \ Xᶜ, ∀ y ∈ Xᶜ \ (X ∪ S), ¬H.Adj x y := by
      intro x hx y hy hxy
      have hxX : x ∈ X := by simpa using hx.2
      have hyX : y ∉ X := hy.1
      have hyS : y ∉ S := fun h => hy.2 (Or.inr h)
      exact hyS ⟨hyX,x,hxX,hxy⟩
    have hb := hsep (X ∪ S) Xᶜ hUW hUl hWl hc
    rw [hU,hinter] at hb
    have hlo : X.ncard ≤ min (X.ncard + S.ncard) Xᶜ.ncard := by
      apply le_min <;> omega
    exact lt_of_le_of_lt hlo hb
  · have hxS : X.ncard ≤ S.ncard := by omega
    change X.ncard < (6*S.ncard+2*t+4)^2
    have hs := Nat.mul_self_le_mul_self
      (show 6*S.ncard+4 ≤ 6*S.ncard+2*t+4 by omega)
    nlinarith

/-- Quantified robust vertex expansion following arbitrary edge deletions. -/
lemma IsVertexMinimal.edge_deletion_boundary_bound (hG : IsVertexMinimal C G)
    (hC : 0 < C) (F : Set (Sym2 V)) (t : ℕ) (hF : F.ncard ≤ C*t)
    (X : Set V) (hhalf : 2 * X.ncard ≤ Fintype.card V) :
    X.ncard < (6 * (externalBoundary (G.deleteEdges F) X).ncard + 2*t+4)^2 :=
  boundary_bound_of_separator_bounds (G.deleteEdges F) t
    (hG.edge_deletion_separator_bound hC F t hF) X hhalf

/-- A convenient quantitative form: if t costs at most one quarter of
sqrt(|X|), the remaining external boundary still has square-root order. -/
lemma IsVertexMinimal.robust_boundary_bound (hG : IsVertexMinimal C G)
    (hC : 0 < C) (F : Set (Sym2 V)) (t : ℕ) (hF : F.ncard ≤ C*t)
    (X : Set V) (hhalf : 2 * X.ncard ≤ Fintype.card V)
    (ht : 4*t+8 ≤ Nat.sqrt X.ncard) :
    Nat.sqrt X.ncard < 12 * (externalBoundary (G.deleteEdges F) X).ncard := by
  have hb := hG.edge_deletion_boundary_bound hC F t hF X hhalf
  have hs := Nat.sqrt_lt'.mpr hb
  omega

end Erdos184.SqrtDeficitSeparator
