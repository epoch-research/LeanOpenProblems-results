import Submission.TwoOddTerminalSeparation
import Submission.SeparatorParity
import Submission.MoveTerminalEdge

/-!
Gluing even-graph cycle bounds across any separator of order at most four.
The matching correction is adaptive; no fixed terminal routing is assumed.
-/
open SimpleGraph
open scoped Classical
namespace Erdos184.FiniteTerminalGluing
open TwoTerminalGluing ExactVertexSmoothing TerminalRouting
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 1500000

/-- In the four-odd case an existing terminal edge can be moved to reduce to
two odd terminals; otherwise all three new matching completions are available. -/
lemma four_odd_separation {G A B : SimpleGraph V} (S : Set V)
    (hS : S.ncard = 4) (hA : A ≤ G) (hB : B ≤ G)
    (hd : Disjoint A.edgeSet B.edgeSet) (hu : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hi : A.support ∩ B.support ⊆ S)
    (heA : ∀ x, Even (A.degree x) ↔ x ∉ S)
    (heB : ∀ x, Even (B.degree x) ↔ x ∉ S) (kA kB : ℕ)
    (hbA : ∀ X : SimpleGraph V, X.support ⊆ A.support →
      (∀ x, Even (X.degree x)) → HasPieceBound kA X)
    (hbB : ∀ X : SimpleGraph V, X.support ⊆ B.support →
      (∀ x, Even (X.degree x)) → HasPieceBound kB X) :
    HasPieceBound (kA+kB+4) G := by
  have move (X Y : SimpleGraph V) (hX : X ≤ G) (hY : Y ≤ G)
      (hdXY : Disjoint X.edgeSet Y.edgeSet) (huXY : X.edgeSet ∪ Y.edgeSet = G.edgeSet)
      (hiXY : X.support ∩ Y.support ⊆ S)
      (heX : ∀ x, Even (X.degree x) ↔ x ∉ S)
      (heY : ∀ x, Even (Y.degree x) ↔ x ∉ S) (kX kY : ℕ)
      (hbX : ∀ Z : SimpleGraph V, Z.support ⊆ X.support →
        (∀ x, Even (Z.degree x)) → HasPieceBound kX Z)
      (hbY : ∀ Z : SimpleGraph V, Z.support ⊆ Y.support →
        (∀ x, Even (Z.degree x)) → HasPieceBound kY Z)
      (a b : V) (ha : a ∈ S) (hb : b ∈ S) (hab : X.Adj a b) :
      HasPieceBound (kX+kY+4) G := by
    obtain ⟨X',Y',hX',hY',hsX',hsY',hd',hu',heX',heY'⟩ :=
      move_terminal_edge S ha hb hX hY hdXY huXY heX heY hab
    have hsub : ({a,b} : Set V) ⊆ S := by
      intro x hx
      rcases hx with rfl | hx
      · exact ha
      · exact hx ▸ hb
    have hcard : (S \ {a,b}).ncard = 2 := by
      have hh := Set.ncard_diff_add_ncard_of_subset hsub
      rw [hS,Set.ncard_pair hab.ne] at hh
      omega
    obtain ⟨c,d,hcd,hcdS⟩ := Set.ncard_eq_two.mp hcard
    have hcX : ∀ x, Even (X'.degree x) ↔ x ≠ c ∧ x ≠ d := by
      simpa only [hcdS,Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using heX'
    have hcY : ∀ x, Even (Y'.degree x) ↔ x ≠ c ∧ x ≠ d := by
      simpa only [hcdS,Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using heY'
    obtain ⟨D,hcD,hdD,hbD⟩ := two_odd_terminal_separation S hcd hcX hcY hX' hY'
      hd' hu' (fun _ hx => hiXY ⟨hsX' hx.1,hsY' hx.2⟩) kX kY
      (fun Z hZ heZ => hbX Z (hZ.trans hsX') heZ)
      (fun Z hZ heZ => hbY Z (hZ.trans hsY') heZ)
    exact ⟨D,hcD,hdD,by omega⟩
  by_cases ha : ∃ a ∈ S, ∃ b ∈ S, A.Adj a b
  · obtain ⟨a,ha,b,hb,hab⟩ := ha
    exact move A B hA hB hd hu hi heA heB kA kB hbA hbB a b ha hb hab
  by_cases hb : ∃ a ∈ S, ∃ b ∈ S, B.Adj a b
  · obtain ⟨a,ha,b,hb,hab⟩ := hb
    have hh := move B A hB hA hd.symm (by rw [Set.union_comm,hu])
      (fun _ hx => hi ⟨hx.2,hx.1⟩) heB heA kB kA hbB hbA a b ha hb hab
    simpa only [Nat.add_comm kA kB] using hh
  obtain ⟨t,ht,htS⟩ := enumerate_four_set S hS
  have hm (i : Fin 4) : t i ∈ S := htS ▸ Set.mem_range_self i
  exact four_odd_terminal_separation t ht hA hB hd hu
    (by rwa [htS]) (by simpa only [htS] using heA) (by simpa only [htS] using heB)
    (fun i j h => ha ⟨t i,hm i,t j,hm j,h⟩)
    (fun i j h => hb ⟨t i,hm i,t j,hm j,h⟩) kA kB hbA hbB

/-- General four-vertex gluing. Bounds are supplied for arbitrary even graphs
on each original side support. Terminal edges need not be absent. -/
lemma decomposition_of_four_separation {G A B : SimpleGraph V} (S : Set V)
    (hS : S.ncard ≤ 4) (heG : ∀ x, Even (G.degree x))
    (hA : A ≤ G) (hB : B ≤ G)
    (hd : Disjoint A.edgeSet B.edgeSet) (hu : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hi : A.support ∩ B.support ⊆ S) (kA kB : ℕ)
    (hbA : ∀ X : SimpleGraph V, X.support ⊆ A.support →
      (∀ x, Even (X.degree x)) → HasPieceBound kA X)
    (hbB : ∀ X : SimpleGraph V, X.support ⊆ B.support →
      (∀ x, Even (X.degree x)) → HasPieceBound kB X) :
    HasPieceBound (kA+kB+4) G := by
  rcases parity_of_four_separation S hS heG hd hu hi with hev | htwo | hfour
  · obtain ⟨DA,hcA,hdA,hbDA⟩ := hbA A le_rfl hev.1
    obtain ⟨DB,hcB,hdB,hbDB⟩ := hbB B le_rfl hev.2
    obtain ⟨D,hcD,hdD,hbD⟩ := combine_pure_decompositions hA hB hd hu
      DA DB hcA hcB hdA hdB
    exact ⟨D,hcD,hdD,by omega⟩
  · obtain ⟨a,b,hab,heA,heB⟩ := htwo
    obtain ⟨D,hcD,hdD,hbD⟩ := two_odd_terminal_separation S hab heA heB hA hB
      hd hu hi kA kB hbA hbB
    exact ⟨D,hcD,hdD,by omega⟩
  · exact four_odd_separation S hfour.1 hA hB hd hu hi hfour.2.1 hfour.2.2 kA kB hbA hbB

/-- Keep the zero overhead of three-terminal gluing in the smaller cases. -/
lemma decomposition_of_small_separation {G A B : SimpleGraph V} (S : Set V)
    (hS : S.ncard ≤ 4) (heG : ∀ x, Even (G.degree x))
    (hA : A ≤ G) (hB : B ≤ G)
    (hd : Disjoint A.edgeSet B.edgeSet) (hu : A.edgeSet ∪ B.edgeSet = G.edgeSet)
    (hi : A.support ∩ B.support ⊆ S) (kA kB : ℕ)
    (hbA : ∀ X : SimpleGraph V, X.support ⊆ A.support →
      (∀ x, Even (X.degree x)) → HasPieceBound kA X)
    (hbB : ∀ X : SimpleGraph V, X.support ⊆ B.support →
      (∀ x, Even (X.degree x)) → HasPieceBound kB X) :
    HasPieceBound (kA+kB+(if S.ncard ≤ 3 then 0 else 4)) G := by
  by_cases hsmall : S.ncard ≤ 3
  · simp only [if_pos hsmall,Nat.add_zero]
    exact ThreeVertexSeparation.decomposition_of_separation S hsmall heG hA hB hd hu hi kA kB hbA hbB
  · simp only [if_neg hsmall]
    exact decomposition_of_four_separation S hS heG hA hB hd hu hi kA kB hbA hbB

end Erdos184.FiniteTerminalGluing
