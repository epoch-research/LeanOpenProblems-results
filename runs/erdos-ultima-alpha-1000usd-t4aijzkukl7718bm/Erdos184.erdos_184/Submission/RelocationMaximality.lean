import Submission.SameTerminalCycleRelocation

/-! Exact criterion for retaining global maximality in a one-cycle relocation. -/
open SimpleGraph
namespace Erdos184Work.OddPaths.FanRelocation
variable {V : Type*} {G : SimpleGraph V}

lemma maximal_iff_equal_cycle_length {L N : List (Piece G)} (hL : Maximal L)
    (hN : Admissible N) {v w : V} (C : G.Walk v v) (D : G.Walk w w)
    (he : (edgeList N ++ D.edges).Perm (edgeList L ++ C.edges)) :
    Maximal N ↔ C.length = D.length := by
  have hlen := he.length_eq
  simp only [List.length_append,Walk.length_edges] at hlen
  constructor
  · intro hM
    have h₁ := hL.2 N hN
    have h₂ := hM.2 L hL.1
    omega
  · intro hCD
    refine ⟨hN,?_⟩
    intro M hM
    have hh := hL.2 M hM
    omega

lemma strict_cycle_growth_loses_coverage {L N : List (Piece G)}
    {v w : V} (C : G.Walk v v) (D : G.Walk w w)
    (he : (edgeList N ++ D.edges).Perm (edgeList L ++ C.edges))
    (hCD : C.length < D.length) :
    (edgeList N).length < (edgeList L).length := by
  have hlen := he.length_eq
  simp only [List.length_append,Walk.length_edges] at hlen
  omega

end Erdos184Work.OddPaths.FanRelocation
#print axioms Erdos184Work.OddPaths.FanRelocation.maximal_iff_equal_cycle_length
#print axioms Erdos184Work.OddPaths.FanRelocation.strict_cycle_growth_loses_coverage
