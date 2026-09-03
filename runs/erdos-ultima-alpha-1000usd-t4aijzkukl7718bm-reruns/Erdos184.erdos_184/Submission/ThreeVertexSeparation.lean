import Submission.ThreeTerminalGluing
import Submission.ShiftedTwoVertexCuts

/-!
A separator of order at most three permits additive combination of pure
cycle bounds for its two sides, allowing parity correction on the separator.
No unconditional linear bound or critical-connectivity conclusion is asserted.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.ThreeVertexSeparation
open TwoTerminalGluing ExactVertexSmoothing

variable {V : Type*} [Fintype V]

/-- An even graph has either zero or two odd side-degrees on a separator
of order at most three. The two odd terminals can be put first. -/
lemma parity_of_separation {G A B : SimpleGraph V} (S : Set V)
    (hS : S.ncard ≤ 3) (heG : ∀ x, Even (G.degree x))
    (hd : Disjoint A.edgeSet B.edgeSet) (hu : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hv : A.support ∩ B.support ⊆ S) :
    ((∀ x, Even (A.degree x)) ∧ (∀ x, Even (B.degree x))) ∨
      ∃ a b c : V, a ≠ b ∧ S ⊆ {a,b,c} ∧
        (∀ x, Even (A.degree x) ↔ x ≠ a ∧ x ≠ b) ∧
        (∀ x, Even (B.degree x) ↔ x ≠ a ∧ x ≠ b) := by
  have heq : A ⊔ B = G := edgeSet_injective (by rw [edgeSet_sup,hu])
  have hpar (x : V) : Even (A.degree x) ↔ Even (B.degree x) := by
    have hh := degree_sup_of_edge_disjoint A B hd x
    have hx := heG x
    simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,heq] at hh hx ⊢
    rw [hh] at hx
    exact Nat.even_add.mp hx
  have hout (x : V) (hxS : x ∉ S) : Even (A.degree x) := by
    by_cases hx : x ∈ A.support
    · have hxB : x ∉ B.support := fun hy => hxS (hv ⟨hx,hy⟩)
      have hh := degree_eq_of_other_unsupported hu x hxB
      have hx := heG x
      simp only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hx ⊢
      rwa [hh]
    · rw [(A.degree_eq_zero_iff_notMem_support x).mpr hx]
      decide
  by_cases hA : ∀ x, Even (A.degree x)
  · exact Or.inl ⟨hA,fun x => (hpar x).mp (hA x)⟩
  let F : Finset V := Finset.univ.filter (fun x => Odd (A.degree x))
  have hF : ∀ x, x ∈ F ↔ ¬Even (A.degree x) := by
    intro x
    simp only [F,Finset.mem_filter,Finset.mem_univ,true_and,Nat.not_even_iff_odd]
  have hFS : (F : Set V) ⊆ S := by
    intro x hx
    by_contra hn
    exact (hF x).mp hx (hout x hn)
  have hcard : F.card ≤ 3 := by
    have hh := (Set.ncard_le_ncard hFS).trans hS
    simpa using hh
  have heven : Even F.card := A.even_card_odd_degree_vertices
  have hpos : 0 < F.card := by
    apply Finset.card_pos.mpr
    push_neg at hA
    obtain ⟨x,hx⟩ := hA
    exact ⟨x,(hF x).mpr hx⟩
  have htwo : F.card = 2 := by
    obtain ⟨k,hk⟩ := heven
    omega
  obtain ⟨a,b,hab,hFab⟩ := Finset.card_eq_two.mp htwo
  have habS : ({a,b} : Set V) ⊆ S := by
    simpa only [hFab,Finset.coe_pair] using hFS
  have hdiff : (S \ {a,b}).ncard ≤ 1 := by
    have hh := Set.ncard_diff_add_ncard_of_subset habS
    rw [Set.ncard_pair hab] at hh
    omega
  letI : Nonempty V := ⟨a⟩
  obtain ⟨c,hc⟩ := (Set.ncard_le_one_iff_subset_singleton (Set.toFinite _)).mp hdiff
  have hSabc : S ⊆ {a,b,c} := by
    intro x hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    by_cases hxb : x = b
    · exact Or.inr (Or.inl hxb)
    exact Or.inr (Or.inr (hc ⟨hx,by simp [hxa,hxb]⟩))
  have hOddA : ∀ x, Even (A.degree x) ↔ x ≠ a ∧ x ≠ b := by
    intro x
    have hh := hF x
    rw [hFab] at hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    tauto
  exact Or.inr ⟨a,b,c,hab,hSabc,hOddA,fun x => (hpar x).symm.trans (hOddA x)⟩

set_option maxHeartbeats 1200000 in
/-- Additive gluing across a separator of order at most three. The hypotheses
supply bounds for arbitrary even graphs on the original side supports,
including the graphs obtained by moving or adding one separator edge. -/
lemma decomposition_of_separation {G A B : SimpleGraph V} (S : Set V)
    (hS : S.ncard ≤ 3) (heG : ∀ x, Even (G.degree x))
    (hA : A ≤ G) (hB : B ≤ G)
    (hdis : Disjoint A.edgeSet B.edgeSet) (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hinter : A.support ∩ B.support ⊆ S) (kA kB : ℕ)
    (hboundA : ∀ X : SimpleGraph V, X.support ⊆ A.support →
      (∀ x, Even (X.degree x)) → HasPieceBound kA X)
    (hboundB : ∀ Y : SimpleGraph V, Y.support ⊆ B.support →
      (∀ x, Even (Y.degree x)) → HasPieceBound kB Y) :
    HasPieceBound (kA+kB) G := by
  have finish (X Y : SimpleGraph V) (hx : X ≤ G) (hy : Y ≤ G)
      (heX : ∀ x, Even (X.degree x)) (heY : ∀ x, Even (Y.degree x))
      (hsX : X.support ⊆ A.support) (hsY : Y.support ⊆ B.support)
      (hdXY : Disjoint X.edgeSet Y.edgeSet) (huXY : X.edgeSet ∪ Y.edgeSet = G.edgeSet) : HasPieceBound (kA+kB) G := by
    obtain ⟨DX,hcX,hdX,hbX⟩ := hboundA X hsX heX
    obtain ⟨DY,hcY,hdY,hbY⟩ := hboundB Y hsY heY
    obtain ⟨D,hcD,hdD,hbD⟩ := combine_pure_decompositions hx hy hdXY huXY DX DY hcX hcY hdX hdY
    exact ⟨D,hcD,hdD,by omega⟩
  rcases parity_of_separation S hS heG hdis hcover hinter with hEven | hOdd
  · exact finish A B hA hB hEven.1 hEven.2 (Set.Subset.refl _) (Set.Subset.refl _) hdis hcover
  obtain ⟨a,b,c,hab,hSabc,hOddA,hOddB⟩ := hOdd
  have hinter' : A.support ∩ B.support ⊆ {a,b,c} := hinter.trans hSabc
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
  obtain ⟨DA,hcA,hdA,hbA⟩ := hboundA (A ⊔ edge a b) hsA
    (by
      intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using even_sup_edge_of_odd_ends hab ha hOddA x)
  obtain ⟨DB,hcB,hdB,hbB⟩ := hboundB (B ⊔ edge a b) hsB
    (by
      intro x
      simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
        using even_sup_edge_of_odd_ends hab hb hOddB x)
  have hnew : (edge a b : SimpleGraph V).Adj a b := by simp [edge_adj,hab]
  have hi : (A ⊔ edge a b).support ∩ (B ⊔ edge a b).support ⊆ {a,b,c} :=
    fun _ h => hinter' ⟨hsA h.1,hsB h.2⟩
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
  obtain ⟨D,hcD,hdD,hbD⟩ := ThreeTerminalGluing.glue_decompositions (G := G) (Or.inr hnew) (Or.inr hnew)
    hi hd hu DA DB hcA hcB hdA hdB
  exact ⟨D,hcD,hdD,by omega⟩

set_option maxHeartbeats 800000 in
/-- Extract the two proper side supports from failure of reachability after
vertex deletion. Degree at least four makes both side supports large enough. -/
lemma induce_compl_reachable_of_no_split (G : SimpleGraph V) (S : Set V)
    (hdegree : ∀ x, 4 ≤ G.degree x)
    (hno : ∀ A B : SimpleGraph V, A ≤ G → B ≤ G →
      Disjoint A.edgeSet B.edgeSet → A.edgeSet ∪ B.edgeSet = G.edgeSet →
      A.support ∩ B.support ⊆ S →
      4 ≤ A.support.ncard → 4 ≤ B.support.ncard →
      A.support.ncard < Fintype.card V → B.support.ncard < Fintype.card V → False)
    (u w : ↥(Sᶜ)) : (G.induce Sᶜ).Reachable u w := by
  by_contra hn
  let R := G.induce Sᶜ
  let T : Set V := {x | x ∈ S ∨ ∃ hx : x ∈ Sᶜ, R.Reachable u ⟨x,hx⟩}
  let A := RankBlocks.sideGraph G T
  let B := G \ A
  have hA : A ≤ G := fun _ _ h => h.1
  have hB : B ≤ G := sdiff_le
  have huT : u.val ∈ T := Or.inr ⟨u.property,Reachable.refl _⟩
  have hwT : w.val ∉ T := by
    rintro (h | ⟨hx,h⟩)
    · exact w.property h
    · exact hn h
  have hclosed {x y : V} (hx : x ∈ T) (hxS : x ∉ S)
      (hxy : G.Adj x y) : y ∈ T := by
    by_cases hyS : y ∈ S
    · exact Or.inl hyS
    obtain ⟨hx',hux⟩ := hx.resolve_left hxS
    have hRxy : R.Adj ⟨x,hx'⟩ ⟨y,hyS⟩ := hxy
    exact Or.inr ⟨hyS,hux.trans hRxy.reachable⟩
  have hdis : Disjoint A.edgeSet B.edgeSet := by
    change Disjoint A.edgeSet (G \ A).edgeSet
    rw [edgeSet_sdiff]
    exact Set.disjoint_sdiff_right
  have hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet := by
    change A.edgeSet ∪ (G \ A).edgeSet = G.edgeSet
    rw [edgeSet_sdiff]
    exact Set.union_diff_cancel (edgeSet_mono hA)
  have hinter : A.support ∩ B.support ⊆ S := by
    rintro x ⟨⟨y,hy⟩,⟨z,hz⟩⟩
    by_contra hxS
    exact hz.2 ⟨hz.1,hy.2.1,hclosed hy.2.1 hxS hz.1⟩
  have hwA : w.val ∉ A.support := by
    rintro ⟨x,hx⟩
    exact hwT hx.2.1
  have huB : u.val ∉ B.support := by
    rintro ⟨x,hx⟩
    exact hx.2 ⟨hx.1,huT,hclosed huT u.property hx.1⟩
  have hAl : A.support.ncard < Fintype.card V := by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
      using Fintype.card_subtype_lt hwA
  have hBl : B.support.ncard < Fintype.card V := by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
      using Fintype.card_subtype_lt huB
  have hnu : G.neighborSet u.val ⊆ A.support := by
    intro x hx
    have hux : A.Adj u.val x := ⟨hx,huT,hclosed huT u.property hx⟩
    exact ⟨u.val,hux.symm⟩
  have hnw : G.neighborSet w.val ⊆ B.support := by
    intro x hx
    have hwx : B.Adj w.val x := ⟨hx,fun h => hwT h.2.1⟩
    exact ⟨w.val,hwx.symm⟩
  have hdu : G.degree u.val ≤ A.support.ncard := by
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using Set.ncard_le_ncard hnu
  have hdw : G.degree w.val ≤ B.support.ncard := by
    simpa only [← card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using Set.ncard_le_ncard hnw
  have hlu := hdegree u.val
  have hlw := hdegree w.val
  exact hno A B hA hB hdis hcover hinter
    (by omega) (by omega) hAl hBl

end Erdos184.ThreeVertexSeparation
