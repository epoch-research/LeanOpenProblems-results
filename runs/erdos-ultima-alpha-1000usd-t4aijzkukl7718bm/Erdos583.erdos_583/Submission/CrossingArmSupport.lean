import Submission.CoreIntervalSplicing

/-! Vertex-disjointness of the valid crossed arm pairs obtained by splitting
one original simple path at a vertex outside the core. -/
namespace Erdos583CrossingArmSupportDevelopment
open SimpleGraph Erdos583Work
open scoped Classical
set_option maxHeartbeats 1600000
set_option Elab.async false

lemma path_card_one_of_ends_eq {V : Type*} {G : SimpleGraph V} {a b : V}
    (P : G.Walk a b) (hp : P.IsPath) (hab : a=b) : P.toSubgraph.verts.ncard=1 := by
  subst b
  rw [(Walk.isPath_iff_eq_nil P).mp hp]
  simp

lemma prefix_arm_avoids_finish {V : Type*} {G : SimpleGraph V} {x a b y : V}
    (A : G.Walk x a) (Q : G.Walk a b) (B : G.Walk b y)
    (hp : (A.append (Q.append B)).IsPath) (S : Set V) (ha : a ∈ S) (hy : y ∉ S) :
    y ∉ A.support := by
  intro hyA
  have hya : y ≠ a := fun h ↦ hy (h ▸ ha)
  exact hp.ne_of_mem_support_of_append hya hyA (Q.append B).end_mem_support rfl

lemma suffix_arm_avoids_start {V : Type*} {G : SimpleGraph V} {x a b y : V}
    (A : G.Walk x a) (Q : G.Walk a b) (B : G.Walk b y)
    (hp : (A.append (Q.append B)).IsPath) (S : Set V) (hb : b ∈ S) (hx : x ∉ S) :
    x ∉ B.support := by
  intro hxB
  have hxb : x ≠ b := fun h ↦ hx (h ▸ hb)
  have hp' : ((A.append Q).append B).IsPath := by simpa only [Walk.append_assoc] using hp
  exact hp'.ne_of_mem_support_of_append hxb (A.append Q).start_mem_support hxB rfl

lemma core_interval_pair_arm_disjoint {V : Type*} {G : SimpleGraph V}
    {x a b y x' a' b' y' z : V}
    (A : G.Walk x a) (Q : G.Walk a b) (B : G.Walk b y)
    (D : G.Walk x' a') (R : G.Walk a' b') (E : G.Walk b' y')
    (hp : (A.append (Q.append B)).IsPath) (hq : (D.append (R.append E)).IsPath)
    (S : Set V) (ha : a ∈ S) (hb : b ∈ S) (ha' : a' ∈ S) (hb' : b' ∈ S)
    (hz : z ∉ S) (hends : (y=z ∧ x'=z) ∨ (x=z ∧ y'=z))
    (hmeet : ∀ w ∈ (A.append (Q.append B)).support,
      w ∈ (D.append (R.append E)).support → w=z) :
    Disjoint {w | w ∈ A.support} {w | w ∈ D.support} ∧
      Disjoint {w | w ∈ B.support} {w | w ∈ E.support} := by
  have hAm : ∀ w ∈ A.support, w ∈ (A.append (Q.append B)).support := by
    intro w hw; exact (A.mem_support_append_iff _).mpr (Or.inl hw)
  have hBm : ∀ w ∈ B.support, w ∈ (A.append (Q.append B)).support := by
    intro w hw; exact (A.mem_support_append_iff _).mpr
      (Or.inr ((Q.mem_support_append_iff B).mpr (Or.inr hw)))
  have hDm : ∀ w ∈ D.support, w ∈ (D.append (R.append E)).support := by
    intro w hw; exact (D.mem_support_append_iff _).mpr (Or.inl hw)
  have hEm : ∀ w ∈ E.support, w ∈ (D.append (R.append E)).support := by
    intro w hw; exact (D.mem_support_append_iff _).mpr
      (Or.inr ((R.mem_support_append_iff E).mpr (Or.inr hw)))
  rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · constructor
    · apply Set.disjoint_left.mpr
      intro w hwA hwD
      have hwz := hmeet w (hAm w hwA) (hDm w hwD)
      exact prefix_arm_avoids_finish A Q B hp S ha hz (hwz ▸ hwA)
    · apply Set.disjoint_left.mpr
      intro w hwB hwE
      have hwz := hmeet w (hBm w hwB) (hEm w hwE)
      exact suffix_arm_avoids_start D R E hq S hb' hz (hwz ▸ hwE)
  · constructor
    · apply Set.disjoint_left.mpr
      intro w hwA hwD
      have hwz := hmeet w (hAm w hwA) (hDm w hwD)
      exact prefix_arm_avoids_finish D R E hq S ha' hz (hwz ▸ hwD)
    · apply Set.disjoint_left.mpr
      intro w hwB hwE
      have hwz := hmeet w (hBm w hwB) (hEm w hwE)
      exact suffix_arm_avoids_start A Q B hp S hb hz (hwz ▸ hwB)

end Erdos583CrossingArmSupportDevelopment
