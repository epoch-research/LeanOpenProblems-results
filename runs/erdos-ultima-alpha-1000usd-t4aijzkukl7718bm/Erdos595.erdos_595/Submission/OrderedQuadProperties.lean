import Submission.OrderedQuadRight
import Submission.NoPrismFinitePalette

/-! Additional verified properties of the ordered-quadruple candidate. -/
set_option autoImplicit false
set_option maxHeartbeats 0
open SimpleGraph Set
namespace Erdos595OrderedQuadRight
open Erdos595ArcAdjoint Erdos595ArcRoundTrip
variable {A : Type*} [LinearOrder A]

theorem unique_triangle : UniqueTriangleEdge (graph A) := by
  intro x y z w hxy hxz hyz hxw hyw
  have hz := triangle_options hxy hxz hyz
  have hw := triangle_options hxy hxw hyw
  rcases hz with hz | hz | hz | hz | hz | hz
  · rcases hw with hw | hw | hw | hw | hw | hw
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      funext n
      fin_cases n
      · exact (Eq.trans h4.symm k4)
      · exact (Eq.trans h0.symm k0)
      · exact (Eq.trans h5.symm k5)
      · exact (Eq.trans h3.symm k3)
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
  · rcases hw with hw | hw | hw | hw | hw | hw
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      funext n
      fin_cases n
      · exact (Eq.trans h4 k4.symm)
      · exact (Eq.trans h5 k5.symm)
      · exact (Eq.trans h1.symm k1)
      · exact (Eq.trans h2.symm k2)
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
  · rcases hw with hw | hw | hw | hw | hw | hw
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      funext n
      fin_cases n
      · exact (Eq.trans h4.symm k4)
      · exact (Eq.trans h0.symm k0)
      · exact (Eq.trans h5.symm k5)
      · exact (Eq.trans h3.symm k3)
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
  · rcases hw with hw | hw | hw | hw | hw | hw
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      funext n
      fin_cases n
      · exact (Eq.trans h0 k0.symm)
      · exact (Eq.trans h1 k1.symm)
      · exact (Eq.trans h2 k2.symm)
      · exact (Eq.trans h3 k3.symm)
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
  · rcases hw with hw | hw | hw | hw | hw | hw
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      funext n
      fin_cases n
      · exact (Eq.trans h4 k4.symm)
      · exact (Eq.trans h5 k5.symm)
      · exact (Eq.trans h1.symm k1)
      · exact (Eq.trans h2.symm k2)
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
  · rcases hw with hw | hw | hw | hw | hw | hw
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      exfalso
      order
    · rcases hz with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
      rcases hw with ⟨k0,k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
      funext n
      fin_cases n
      · exact (Eq.trans h0 k0.symm)
      · exact (Eq.trans h1 k1.symm)
      · exact (Eq.trans h2 k2.symm)
      · exact (Eq.trans h3 k3.symm)

/-- The base itself has a two-color triangle-avoiding edge coloring. -/
theorem base_two : Erdos595FinitePalette.HasColoring (graph A) Bool :=
  Erdos595NoPrismFinitePalette.base_two (graph A) unique_triangle

private instance (x y : Quad (Fin 8)) : Decidable (AB x y) := by unfold AB; infer_instance
private instance (x y : Quad (Fin 8)) : Decidable (AC x y) := by unfold AC; infer_instance
private instance (x y : Quad (Fin 8)) : Decidable (BC x y) := by unfold BC; infer_instance

private instance : DecidableRel (graph (Fin 8)).Adj := fun x y =>
  inferInstanceAs (Decidable (AB x y ∨ AC x y ∨ AB y x ∨ BC x y ∨ AC y x ∨ BC y x))

/-- Unlike the first matched-pair pattern, this pattern contains a
triangular prism. Thus the earlier no-prism covering theorem does not apply. -/
theorem has_prism : ¬Erdos595NoPrismRight.NoPrism (graph (Fin 8)) := by
  intro h
  apply h ![1,3,4,7] ![0,2,3,4] ![0,1,2,7]
    ![1,4,5,6] ![0,1,2,6] ![0,2,4,5]
  all_goals try decide +kernel
  apply Set.disjoint_left.mpr
  intro a ha hb
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with hb | hb | hb <;>
    norm_num [funext_iff,Fin.forall_fin_succ] at hb <;> omega

#print axioms unique_triangle
#print axioms base_two
#print axioms has_prism
end Erdos595OrderedQuadRight
