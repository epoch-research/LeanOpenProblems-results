import Submission.GraphTwoCutTheory

/-! Applying the fresh-closure two-edge-cut theorem to an arbitrary vertex partition. -/
open SimpleGraph
open scoped Classical
namespace Erdos184Work.GraphTwoCut
open GraphIsoCore Critical EvenCore Rigidity
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def partitionIso (G : SimpleGraph V) (S : Set V)
    (a b : S) (c d : (Sᶜ : Set V))
    (hcut : ∀ x : S, ∀ y : (Sᶜ : Set V), G.Adj x.val y.val ↔
      (x = a ∧ y = c) ∨ (x = b ∧ y = d)) :
    join (G.induce S) (G.induce Sᶜ) a b c d ≃g G where
  toEquiv := Equiv.Set.sumCompl S
  map_rel_iff' := by
    intro x y
    cases x with
    | inl x =>
      cases y with
      | inl y => rfl
      | inr y => exact hcut x y
    | inr x =>
      cases y with
      | inl y =>
        change G.Adj x.val y.val ↔ _
        rw [SimpleGraph.adj_comm]
        exact hcut y x
      | inr y => rfl

lemma partition_closures_even (G : SimpleGraph V) (S : Set V)
    (a b : S) (c d : (Sᶜ : Set V)) (hsep : a ≠ b ∨ c ≠ d)
    (hcut : ∀ x : S, ∀ y : (Sᶜ : Set V), G.Adj x.val y.val ↔
      (x = a ∧ y = c) ∨ (x = b ∧ y = d))
    (he : ∀ x, Even (G.degree x)) :
    (∀ x, Even ((closure (G.induce S) a b).degree x)) ∧
      (∀ x, Even ((closure (G.induce Sᶜ) c d).degree x)) := by
  have hj := even_iso (partitionIso G S a b c d hcut).symm he
  exact closures_even _ _ hsep hj

lemma number_two_edge_cut (G : SimpleGraph V) (S : Set V)
    (a b : S) (c d : (Sᶜ : Set V)) (hsep : a ≠ b ∨ c ≠ d)
    (hcut : ∀ x : S, ∀ y : (Sᶜ : Set V), G.Adj x.val y.val ↔
      (x = a ∧ y = c) ∨ (x = b ∧ y = d))
    (he : ∀ x, Even (G.degree x)) :
    number G = number (closure (G.induce S) a b) + number (closure (G.induce Sᶜ) c d) - 1 := by
  have e := partitionIso G S a b c d hcut
  have hj := even_iso e.symm he
  exact (BlockRestriction.number_eq_of_iso e).symm.trans (number_join _ _ hsep hj)

lemma minimal_two_edge_cut_iff (G : SimpleGraph V) (S : Set V)
    (a b : S) (c d : (Sᶜ : Set V)) (hsep : a ≠ b ∨ c ≠ d)
    (hcut : ∀ x : S, ∀ y : (Sᶜ : Set V), G.Adj x.val y.val ↔
      (x = a ∧ y = c) ∨ (x = b ∧ y = d))
    (he : ∀ x, Even (G.degree x)) :
    EvenMinimal G ↔ EvenMinimal (closure (G.induce S) a b) ∧ EvenMinimal (closure (G.induce Sᶜ) c d) := by
  have e := partitionIso G S a b c d hcut
  have hj := even_iso e.symm he
  exact (minimal_iso_iff e).symm.trans (minimal_join_iff _ _ hsep hj)

lemma rigid_two_edge_cut_iff (G : SimpleGraph V) (S : Set V)
    (a b : S) (c d : (Sᶜ : Set V)) (hsep : a ≠ b ∨ c ≠ d)
    (hcut : ∀ x : S, ∀ y : (Sᶜ : Set V), G.Adj x.val y.val ↔
      (x = a ∧ y = c) ∨ (x = b ∧ y = d))
    (he : ∀ x, Even (G.degree x)) :
    CycleRigid G ↔ CycleRigid (closure (G.induce S) a b) ∧ CycleRigid (closure (G.induce Sᶜ) c d) := by
  have e := partitionIso G S a b c d hcut
  have hj := even_iso e.symm he
  exact (rigid_iso_iff e hj).symm.trans (rigid_join_iff _ _ hsep hj)

lemma nonrigid_minimal_two_edge_cut_factor (G : SimpleGraph V) (S : Set V)
    (a b : S) (c d : (Sᶜ : Set V)) (hsep : a ≠ b ∨ c ≠ d)
    (hcut : ∀ x : S, ∀ y : (Sᶜ : Set V), G.Adj x.val y.val ↔
      (x = a ∧ y = c) ∨ (x = b ∧ y = d))
    (he : ∀ x, Even (G.degree x)) (hm : EvenMinimal G) (hn : ¬ CycleRigid G) :
    (EvenMinimal (closure (G.induce S) a b) ∧ ¬ CycleRigid (closure (G.induce S) a b)) ∨
      (EvenMinimal (closure (G.induce Sᶜ) c d) ∧ ¬ CycleRigid (closure (G.induce Sᶜ) c d)) := by
  have e := partitionIso G S a b c d hcut
  have hj := even_iso e.symm he
  exact nonrigid_minimal_join_factor _ _ hsep hj ((minimal_iso_iff e).mpr hm)
    (fun hr => hn ((rigid_iso_iff e hj).mp hr))

#print axioms partitionIso
#print axioms number_two_edge_cut
#print axioms minimal_two_edge_cut_iff
#print axioms rigid_two_edge_cut_iff
#print axioms nonrigid_minimal_two_edge_cut_factor
end Erdos184Work.GraphTwoCut
