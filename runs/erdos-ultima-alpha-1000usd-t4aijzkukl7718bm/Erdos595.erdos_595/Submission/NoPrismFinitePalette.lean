import Submission.NoPrismRightCover
import Submission.SmallMarkedFinitePalette

/-! The no-prism right-adjoint class in fact has a uniform two-piece cover.
This excludes that class of candidates; it does not settle Erdős 595. -/
set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595NoPrismFinitePalette
open Erdos595Work Erdos595ArcAdjoint Erdos595ArcRoundTrip
open Erdos595MatchingBundle Erdos595FinitePalette Erdos595NoPrismRight
open Erdos595SmallMarkedFinitePalette (of_ordered_patterns)
variable {V C : Type*} (H : SimpleGraph V)

/-- Triangles are edge-disjoint, so one edge from each can receive the other color. -/
theorem base_two (hU : UniqueTriangleEdge H) : HasColoring H Bool := by
  classical
  letI : LinearOrder V := IsWellOrder.linearOrder WellOrderingRel
  let code (a b : V) : Bool := decide (∃ t, H.Adj a t ∧ H.Adj b t ∧ t < a ∧ t < b)
  apply of_ordered_patterns H code
  intro a b c hab hbc hab' hac' hbc' hm
  have hk : code b c = true :=
    decide_eq_true ⟨a,hab'.symm,hac'.symm,hab,hab.trans hbc⟩
  obtain ⟨t,hat,hbt,hta,_⟩ := of_decide_eq_true (hm.2.trans hk)
  have hct := hU hab' hac' hbc' hat hbt
  rw [← hct] at hta
  exact (lt_asymm (hab.trans hbc) hta)

/-- Any nonempty palette transfers without enlargement when all right
triangles consist of stars. Edges outside triangles impose no restriction. -/
theorem star_palette [Nonempty C]
    (hs : ∀ {p q r : Biclique H}, (right H).Adj p q → (right H).Adj p r →
      (right H).Adj q r → Star H p)
    (hH : HasColoring H C) : HasColoring (right H) C := by
  classical
  obtain ⟨c,hc⟩ := hH
  letI : LinearOrder (Biclique H) := IsWellOrder.linearOrder WellOrderingRel
  let code (p q : Biclique H) : C :=
    if hp : Star H p then
      if hq : Star H q then c s(center H p hp,center H q hq) else Classical.arbitrary C
    else Classical.arbitrary C
  apply of_ordered_patterns (right H) code
  intro p q r _ _ hpq hpr hqr hm
  have hp := hs hpq hpr hqr
  have hq := hs hpq.symm hqr hpr
  have hr := hs hpr.symm hqr.symm hpq
  simp only [code,dif_pos hp,dif_pos hq,dif_pos hr] at hm
  exact hc (center H p hp) (center H q hq) (center H r hr)
    (centers_adj H (six H hpq hpr hqr) hp hq)
    (centers_adj H (six H hpr hpq hqr.symm) hp hr)
    (centers_adj H (six H hqr hpq.symm hpr.symm) hq hr) hm

theorem right_two (hU : UniqueTriangleEdge H) (hP : NoPrism H) :
    HasColoring (right H) Bool :=
  star_palette H (triangle_star H hU hP) (base_two H hU)

/-- The limitation is already witnessed by a finite K4-free source. -/
theorem finite_representation_failure :
    ∃ (A : Type) (_ : Finite A) (G : SimpleGraph A), G.CliqueFree 4 ∧
      ∀ (V : Type) (H : SimpleGraph V), UniqueTriangleEdge H → NoPrism H →
        ¬Nonempty (arcGraph G →g H) := by
  obtain ⟨A,hA,G,hG,hbad⟩ := Erdos595FiniteFolkman.finite_folkman Bool
  refine ⟨A,hA,G,hG,?_⟩
  intro V H hU hP ⟨f⟩
  exact hbad ((right_two H hU hP).comap (toRight f))

#print axioms base_two
#print axioms star_palette
#print axioms right_two
#print axioms finite_representation_failure
end Erdos595NoPrismFinitePalette
