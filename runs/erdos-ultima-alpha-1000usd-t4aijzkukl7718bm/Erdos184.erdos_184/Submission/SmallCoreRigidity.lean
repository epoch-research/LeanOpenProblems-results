import Submission.SevenGraphFamily
import Submission.RigidityDegree

/-! Rigidity of even-minimal graphs with cycle decomposition number at most three.
This is a small-optimum result, not a uniform bound for arbitrary graphs. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.SmallCoreRigidity
open Critical EvenCore Rigidity
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma rigid_of_number_le_three (he : ∀ v, Even (G.degree v))
    (hm : EvenMinimal G) (hn : number G ≤ 3) : CycleRigid G := by
  by_cases h : number G ≤ 2
  · exact rigid_of_evenMinimal_number_le_two he hm h
  · exact SevenGraphFamily.three_core_rigid he hm (by omega)

lemma number_ge_four_of_nonrigid (he : ∀ v, Even (G.degree v))
    (hm : EvenMinimal G) (hr : ¬ CycleRigid G) : 4 ≤ number G := by
  by_contra h
  exact hr (rigid_of_number_le_three he hm (by omega))

lemma hereditary_of_number_le_three (he : ∀ v, Even (G.degree v))
    (hm : EvenMinimal G) (hn : number G ≤ 3)
    {R : SimpleGraph V} (hRG : R ≤ G) (hR : ∀ v, Even (R.degree v)) :
    EvenMinimal R :=
  ((rigid_of_number_le_three he hm hn).mono he hRG hR).evenMinimal hR

lemma degree_two_of_number_le_three (he : ∀ v, Even (G.degree v))
    (hm : EvenMinimal G) (hn : number G ≤ 3) (hG : G ≠ ⊥) :
    ∃ v, G.degree v = 2 :=
  CycleRings.rigid_has_degree_two (rigid_of_number_le_three he hm hn) he hG

#print axioms rigid_of_number_le_three
#print axioms number_ge_four_of_nonrigid
#print axioms hereditary_of_number_le_three
#print axioms degree_two_of_number_le_three
end Erdos184Work.SmallCoreRigidity
