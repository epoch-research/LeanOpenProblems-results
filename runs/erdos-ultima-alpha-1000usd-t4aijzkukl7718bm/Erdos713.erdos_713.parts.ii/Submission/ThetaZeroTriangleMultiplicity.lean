import FormalConjecturesUtil
import Submission.ThetaRigidChargeExample

/-! A diagnostic for a proposed zero-triangle charge. The same zero triangle
can witness arbitrarily many different heavy pairs, even under rigidity.
This is not a counterexample to the light-budget density gap or to Erdős 713. -/
open Finset
open scoped Classical
namespace Erdos713ThetaZeroTriangleMultiplicity
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaAnchorPacking Erdos713ThetaPrivatePetals
open Erdos713ThetaRigidChargeExample

lemma hubs_codegree_zero (N r : ℕ) {s t : Fin 3} (hst : s ≠ t) :
    codegree (Inc N r) (hub s) (hub t) = 0 := by
  letI : IsEmpty {a : Rows N // Inc N r a (hub s) ∧ Inc N r a (hub t)} :=
    ⟨fun a => hst (a.property.1.symm.trans a.property.2)⟩
  exact Nat.card_of_isEmpty

lemma hub_private (N r : ℕ) (i : Fin N) (s : Fin 3) :
    hub s ∈ privatePetal (Inc N r) univ (anchor i 0,anchor i 1) (s,i) := by
  rw [mem_privatePetal]
  refine ⟨rfl,by simp [hub,anchor],by simp [hub,anchor],?_⟩
  intro a ha hne hh
  exact hne (Prod.ext hh (mem_filter.mp ha).2.1)

lemma anchor_pairs_injective (N r : ℕ) :
    Function.Injective (fun i : Fin N =>
      ((anchor i 0,anchor i 1) : Cols N r × Cols N r)) := by
  intro i j he
  have h := congrArg Prod.fst he
  exact congrArg Prod.fst (Sum.inl.inj (Sum.inr.inj h))

/-- All N different heavy pairs use the same three distinct private hubs.
Their supporting rows have degree r+3, so none is an exact-pair row. -/
theorem common_triangle (N r : ℕ) :
    ¬ HasTheta (Inc N r) ∧
    (∀ a b, a ≠ b → (row (Inc N r) a ∩ row (Inc N r) b).card ≤ 2) ∧
    (∀ a, (row (Inc N r) a).card = r+3) ∧
    ∃ p : Fin N → Cols N r × Cols N r,
      Function.Injective p ∧
      ∃ z : Fin 3 → Cols N r, Function.Injective z ∧
        (∀ s t, s ≠ t → codegree (Inc N r) (z s) (z t) = 0) ∧
        ∀ i, (p i).1 ≠ (p i).2 ∧
          codegree (Inc N r) (p i).1 (p i).2 = 3 ∧
          ∃ a : Fin 3 → Rows N, Function.Injective a ∧
            ∀ s, a s ∈ commonRows (Inc N r) univ (p i) ∧
              z s ∈ privatePetal (Inc N r) univ (p i) (a s) := by
  refine ⟨no_theta N r,rigid N r,row_card N r,
    (fun i => (anchor i 0,anchor i 1)),anchor_pairs_injective N r,
    hub,?_,?_,?_⟩
  · intro s t he
    exact Sum.inl.inj he
  · exact fun s t hst => hubs_codegree_zero N r hst
  · intro i
    refine ⟨?_,anchor_codegree N r i,(fun s => (s,i)),?_,?_⟩
    · exact fun he => (by decide : (0 : Fin 2) ≠ 1) (anchor_injective i he)
    · intro s t he
      exact congrArg Prod.fst he
    · intro s
      exact ⟨mem_filter.mpr ⟨mem_univ _,rfl,rfl⟩,hub_private N r i s⟩

#print axioms common_triangle
end Erdos713ThetaZeroTriangleMultiplicity
