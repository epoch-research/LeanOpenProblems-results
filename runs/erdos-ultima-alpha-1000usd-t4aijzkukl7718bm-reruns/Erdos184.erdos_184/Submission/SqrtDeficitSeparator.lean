import Submission.ForestSeparatorGluing
import Submission.ShiftedCritical

/-! A square-root deficit normalization and growing-separator restrictions.
These are necessary conditions for a counterexample, not a proof of Erdős 184. -/
open SimpleGraph Filter
open scoped Classical
namespace Erdos184.SqrtDeficitSeparator
open ExactVertexSmoothing
universe u
set_option maxHeartbeats 1000000

/-- A nonconstant deficit in an otherwise linear charge. -/
def deficit (n : ℕ) : ℕ := 2 * n - Nat.sqrt n

def HasBound {V : Type*} [Fintype V] (C : ℕ) (G : SimpleGraph V) : Prop :=
  HasPieceBound (C * deficit (Fintype.card V)) G

lemma deficit_le (n : ℕ) : deficit n ≤ 2*n := Nat.sub_le _ _

lemma deficit_mono : Monotone deficit := by
  apply monotone_nat_of_le_succ
  intro n
  have h := Nat.sqrt_succ_le_succ_sqrt n
  simp only [Nat.succ_eq_add_one] at h
  have hn := Nat.sqrt_le_self n
  dsimp [deficit]
  omega

lemma le_deficit (n : ℕ) : n ≤ deficit n := by
  have h := Nat.sqrt_le_self n
  dsimp [deficit]
  omega

lemma deficit_succ (n : ℕ) : deficit n + 1 ≤ deficit (n+1) := by
  have h := Nat.sqrt_succ_le_succ_sqrt n
  simp only [Nat.succ_eq_add_one] at h
  have hn := Nat.sqrt_le_self n
  dsimp [deficit]
  omega

lemma hasBound_bot {V : Type*} [Fintype V] (C : ℕ) :
    HasBound C (⊥ : SimpleGraph V) :=
  ⟨∅,by simp,by simp [IsDecomposition],by simp⟩

/-- This normalization is equivalent to the unchanged asymptotic conjecture. -/
theorem conjecture_iff_sqrt_deficit_bound :
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
    by_cases hb : G = ⊥
    · subst G
      exact hasBound_bot _
    obtain ⟨D,hD,hd,hcard⟩ := hc G he
    refine ⟨D,hD,hd,?_⟩
    have hbound : (D.card : ℝ) ≤ (N * deficit (Fintype.card V) : ℕ) := by
      calc
        (D.card : ℝ) ≤ c * Fintype.card V := hcard
        _ ≤ (N : ℝ) * Fintype.card V :=
          mul_le_mul_of_nonneg_right hN (by positivity)
        _ ≤ (N : ℝ) * (deficit (Fintype.card V) : ℕ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact_mod_cast le_deficit (Fintype.card V)
        _ = _ := by push_cast; ring
    exact_mod_cast hbound
  · rintro ⟨C,hC⟩
    refine ⟨2*C,?_⟩
    intro V _ _ G he
    obtain ⟨D,hD,hd,hcard⟩ := hC G he
    refine ⟨D,hD,hd,?_⟩
    have hn := hcard.trans (Nat.mul_le_mul_left C (deficit_le (Fintype.card V)))
    have hn' : D.card ≤ (2*C)*Fintype.card V := by nlinarith
    exact_mod_cast hn' 

/-- An elementary floor-square-root concavity estimate, with rounding slack. -/
lemma sqrt_sum_gap {a b n : ℕ} (hab : a ≤ b) (hn : n ≤ a+b) :
    2 * Nat.sqrt n ≤ 2 * Nat.sqrt b + Nat.sqrt a + 4 := by
  have hpq := Nat.sqrt_le_sqrt hab
  have hp := Nat.lt_succ_sqrt' a
  have hq := Nat.lt_succ_sqrt' b
  have hr := Nat.sqrt_le' n
  have hpq' := Nat.mul_le_mul_left (Nat.sqrt a) hpq
  by_contra! hbad
  have hsq := Nat.mul_self_le_mul_self (Nat.le_of_lt hbad)
  nlinarith

/-- The growing-separator budget. No estimate on graph density is used. -/
lemma separator_budget {C a b n s : ℕ} (hC : 0 < C)
    (hlo : n ≤ a+b) (hhi : a+b ≤ n+s)
    (hs : 6*s+4 ≤ Nat.sqrt (min a b)) :
    C * deficit a + C * deficit b + (s-1) ≤ C * deficit n := by
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
  have hgap : Nat.sqrt n + 3*s ≤ Nat.sqrt a + Nat.sqrt b := by
    have hm := min_add_max (Nat.sqrt a) (Nat.sqrt b)
    omega
  have ha := Nat.sqrt_le_self a
  have hb := Nat.sqrt_le_self b
  have hn := Nat.sqrt_le_self n
  have hc : 1 ≤ C := hC
  have hdiff : deficit a + deficit b + s ≤ deficit n := by
    dsimp [deficit]
    omega
  have hmul := Nat.mul_le_mul_left C hdiff
  have hcs := Nat.mul_le_mul_right s hc
  have hsub := Nat.sub_le s 1
  nlinarith

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
    HasPieceBound (C * deficit A.support.ncard) A := by
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
    HasPieceBound (C * deficit S.ncard) A := by
  have hc := Set.ncard_le_ncard hs
  obtain ⟨D,hD,hd,hb⟩ := hG.bound_on_smaller_support A (hc.trans_lt hlt) he
  exact ⟨D,hD,hd,hb.trans (Nat.mul_le_mul_left C (deficit_mono hc))⟩

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
    (Nat.mul_le_mul_left C (deficit_mono hlt.le))⟩

/-- The extra linear slope prevents the square-root rounding jumps from
destroying the minimum-degree reduction. -/
lemma IsVertexMinimal.degree_lower (hG : IsVertexMinimal C G) (hC : 0 < C)
    (v : V) : 2 * (C+2) ≤ G.degree v := by
  have hcard : Fintype.card V = Fintype.card (VertexSmoothing.Without v) + 1 := by
    rw [← Fintype.card_option]
    exact Fintype.card_congr (Equiv.optionSubtypeNe v).symm
  let B := C * deficit (Fintype.card (VertexSmoothing.Without v))
  have hsmall : ∀ H : SimpleGraph (VertexSmoothing.Without v),
      (∀ x, Even (H.degree x)) → HasPieceBound B H := by
    intro H heH
    exact hG.2.2 H (Fintype.card_subtype_lt (x := v) (by simp)) heH
  have hBC : B + C ≤ C * deficit (Fintype.card V) := by
    rw [hcard]
    have hh := Nat.mul_le_mul_left C (deficit_succ
      (Fintype.card (VertexSmoothing.Without v)))
    dsimp only [B]
    nlinarith
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

/-- No separation with a sufficiently small square-root-scale overlap.
The chosen vertex sets can contain isolated vertices of their sides. -/
lemma IsVertexMinimal.no_set_separation (hG : IsVertexMinimal C G) (hC : 0 < C)
    (A B : SimpleGraph V) (U W : Set V)
    (hA : A ≤ G) (hB : B ≤ G)
    (hd : Disjoint A.edgeSet B.edgeSet) (hu : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hAU : A.support ⊆ U) (hBW : B.support ⊆ W) (hUW : U ∪ W = Set.univ)
    (hUl : U.ncard < Fintype.card V) (hWl : W.ncard < Fintype.card V)
    (hsmall : 6 * (U ∩ W).ncard + 4 ≤ Nat.sqrt (min U.ncard W.ncard)) : False := by
  have hn := Set.ncard_union_add_ncard_inter U W
  rw [hUW,Set.ncard_univ,Nat.card_eq_fintype_card] at hn
  have hb := separator_budget hC
    (by omega : Fintype.card V ≤ U.ncard + W.ncard)
    (by omega : U.ncard + W.ncard ≤ Fintype.card V + (U ∩ W).ncard) hsmall
  obtain ⟨D,hD,hdec,hcard⟩ := ForestBoundaryBudget.decomposition_of_finite_separation
    (U ∩ W) hG.1 hA hB hd hu
    (fun _ hx => ⟨hAU hx.1,hBW hx.2⟩)
    (C * deficit U.ncard) (C * deficit W.ncard)
    (fun X hX he => hG.bound_on_support_subset X U
      ((support_mono hX).trans hAU) hUl he)
    (fun X hX he => hG.bound_on_support_subset X W
      ((support_mono hX).trans hBW) hWl he)
  exact hG.2.1 ⟨D,hD,hdec,hcard.trans hb⟩

/-- Equivalently, the smaller side of every proper separation has order
strictly less than a quadratic in the separator size. -/
lemma IsVertexMinimal.separation_side_bound (hG : IsVertexMinimal C G) (hC : 0 < C)
    (A B : SimpleGraph V) (U W : Set V)
    (hA : A ≤ G) (hB : B ≤ G)
    (hd : Disjoint A.edgeSet B.edgeSet) (hu : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hAU : A.support ⊆ U) (hBW : B.support ⊆ W) (hUW : U ∪ W = Set.univ)
    (hUl : U.ncard < Fintype.card V) (hWl : W.ncard < Fintype.card V) :
    min U.ncard W.ncard < (6 * (U ∩ W).ncard + 4)^2 := by
  by_contra! hlarge
  exact hG.no_set_separation hC A B U W hA hB hd hu hAU hBW hUW hUl hWl
    (Nat.le_sqrt'.mpr hlarge)

/-- The same restriction stated solely in terms of vertex sets and absent
cross edges, with no preselected edge partition. -/
lemma IsVertexMinimal.vertex_separator_bound (hG : IsVertexMinimal C G) (hC : 0 < C)
    (U W : Set V) (hUW : U ∪ W = Set.univ)
    (hUl : U.ncard < Fintype.card V) (hWl : W.ncard < Fintype.card V)
    (hcross : ∀ x ∈ U \ W, ∀ y ∈ W \ U, ¬G.Adj x y) :
    min U.ncard W.ncard < (6 * (U ∩ W).ncard + 4)^2 := by
  let A := RankBlocks.sideGraph G U
  let B := G \ A
  have hA : A ≤ G := fun _ _ h => h.1
  have hB : B ≤ G := sdiff_le
  have hd : Disjoint A.edgeSet B.edgeSet := by
    change Disjoint A.edgeSet (G \ A).edgeSet
    rw [edgeSet_sdiff]
    exact Set.disjoint_sdiff_right
  have hu : A.edgeSet ∪ B.edgeSet = G.edgeSet := by
    change A.edgeSet ∪ (G \ A).edgeSet = G.edgeSet
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
  exact hG.separation_side_bound hC A B U W hA hB hd hu hAU hBW hUW hUl hWl

/-- Neighbors outside a vertex set. -/
def externalBoundary (G : SimpleGraph V) (X : Set V) : Set V :=
  {y | y ∉ X ∧ ∃ x ∈ X, G.Adj x y}

/-- Every set of at most half the vertices in a minimal counterexample has
an external neighborhood of square-root scale, up to an explicit offset. -/
lemma IsVertexMinimal.external_boundary_bound (hG : IsVertexMinimal C G)
    (hC : 0 < C) (X : Set V) (hhalf : 2 * X.ncard ≤ Fintype.card V) :
    X.ncard < (6 * (externalBoundary G X).ncard + 4)^2 := by
  let S := externalBoundary G X
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
    have hc : ∀ x ∈ (X ∪ S) \ Xᶜ, ∀ y ∈ Xᶜ \ (X ∪ S), ¬G.Adj x y := by
      intro x hx y hy hxy
      have hxX : x ∈ X := by simpa using hx.2
      have hyX : y ∉ X := hy.1
      have hyS : y ∉ S := fun h => hy.2 (Or.inr h)
      exact hyS ⟨hyX,x,hxX,hxy⟩
    have hb := hG.vertex_separator_bound hC (X ∪ S) Xᶜ hUW hUl hWl hc
    rw [hU,hinter] at hb
    have hlo : X.ncard ≤ min (X.ncard + S.ncard) Xᶜ.ncard := by
      apply le_min <;> omega
    exact lt_of_le_of_lt hlo hb
  · have hxS : X.ncard ≤ S.ncard := by omega
    change X.ncard < (6*S.ncard+4)^2
    nlinarith

end Erdos184.SqrtDeficitSeparator
