import Submission.FiniteTerminalGluing
import Submission.ShiftedTwoVertexCuts

/-! Parity-corrected gluing with two odd terminals. -/
open SimpleGraph
open scoped Classical
namespace Erdos184.FiniteTerminalGluing
open TwoTerminalGluing ExactVertexSmoothing
variable {V : Type*} [Fintype V]

set_option maxHeartbeats 1200000 in
/-- Gluing across a finite separator with exactly two odd side terminals. -/
lemma two_odd_terminal_separation {G A B : SimpleGraph V} (S : Set V)
    {a b : V} (hab : a ≠ b)
    (hOddA : ∀ x, Even (A.degree x) ↔ x ≠ a ∧ x ≠ b)
    (hOddB : ∀ x, Even (B.degree x) ↔ x ≠ a ∧ x ≠ b)
    (hA : A ≤ G) (hB : B ≤ G)
    (hdis : Disjoint A.edgeSet B.edgeSet) (hcover : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hinter : A.support ∩ B.support ⊆ S) (kA kB : ℕ)
    (hboundA : ∀ X : SimpleGraph V, X.support ⊆ A.support →
      (∀ x, Even (X.degree x)) → HasPieceBound kA X)
    (hboundB : ∀ Y : SimpleGraph V, Y.support ⊆ B.support →
      (∀ x, Even (Y.degree x)) → HasPieceBound kB Y) :
    HasPieceBound (kA+kB+(S.ncard-3)) G := by
  have finish (X Y : SimpleGraph V) (hx : X ≤ G) (hy : Y ≤ G)
      (heX : ∀ x, Even (X.degree x)) (heY : ∀ x, Even (Y.degree x))
      (hsX : X.support ⊆ A.support) (hsY : Y.support ⊆ B.support)
      (hdXY : Disjoint X.edgeSet Y.edgeSet) (huXY : X.edgeSet ∪ Y.edgeSet = G.edgeSet) : HasPieceBound (kA+kB+(S.ncard-3)) G := by
    obtain ⟨DX,hcX,hdX,hbX⟩ := hboundA X hsX heX
    obtain ⟨DY,hcY,hdY,hbY⟩ := hboundB Y hsY heY
    obtain ⟨D,hcD,hdD,hbD⟩ := combine_pure_decompositions hx hy hdXY huXY DX DY hcX hcY hdX hdY
    exact ⟨D,hcD,hdD,by omega⟩
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
  have hi : (A ⊔ edge a b).support ∩ (B ⊔ edge a b).support ⊆ S :=
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
  obtain ⟨D,hcD,hdD,hbD⟩ := FiniteTerminalGluing.glue_decompositions (G := G) S (Or.inr hnew) (Or.inr hnew)
    hi hd hu DA DB hcA hcB hdA hdB
  exact ⟨D,hcD,hdD,by omega⟩

end Erdos184.FiniteTerminalGluing
