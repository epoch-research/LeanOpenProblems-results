import Submission.DirectedOrRightCover
import Submission.AllSecondShiftCover

/-!
Countable K4-free homomorphism targets impose a stronger cardinal restriction
than countable proper colorability on the first two ordered shifts. The index
of a first shift must be countable; the index of a second shift must inject
into Set N. These statements concern arbitrary linear orders.
-/
set_option autoImplicit false
open Set SimpleGraph
namespace Erdos595OrderedShiftTarget
open Erdos595DirectedRight Erdos595DirectedOrRight
open Erdos595MiddleCorner Erdos595Work
variable {A W : Type*} [LinearOrder A] [Countable W]

lemma coloring_injective {C : Type*}
    (c : (orGraph (fun a b : A => a < b) (fun a => lt_irrefl a)).Coloring C) :
    Function.Injective c := by
  intro a b he
  rcases lt_trichotomy a b with h | h | h
  · exact False.elim (c.valid (Or.inl h) he)
  · exact h
  · exact False.elim (c.valid (Or.inr h) he)

/-- Countable proper colorability of the shift does NOT imply this stronger
index bound; a countable K4-free homomorphism target does. -/
theorem first_index (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (f : orderedShiftGraph A →g H) : Nonempty (A ↪ ℕ) := by
  obtain ⟨c⟩ := one_pullback (R := fun a b : A => a < b) (fun a => lt_irrefl a)
    H hH f (fun e d h => f.map_adj (Or.inl h))
  exact ⟨⟨c,coloring_injective c⟩⟩

abbrev OrderArc₂ (A : Type*) [LinearOrder A] :=
  Arc (arc (fun a b : A => a < b))

def triple (e : OrderArc₂ A) : Triple A :=
  ⟨e.val.1.val.1,e.val.1.val.2,e.val.2.val.2,e.val.1.property,by
    have he : e.val.1.val.2 = e.val.2.val.1 := e.property
    rw [he]
    exact e.val.2.property⟩

lemma triple_step (e d : OrderArc₂ A)
    (hed : arc (arc (fun a b : A => a < b)) e d) :
    (oneGraph A).Adj (triple e) (triple d) := by
  have he : e.val.1.val.2 = e.val.2.val.1 := e.property
  have hd : e.val.2 = d.val.1 := hed
  exact Or.inl ⟨he.trans (congrArg (fun a => a.val.1) hd),
    congrArg (fun a => a.val.2) hd⟩

/-- A countable K4-free target for the second shift gives a SINGLE powerset
encoding of its index, instead of the two powersets for arbitrary proper
countable vertex colorings. -/
theorem second_index (H : SimpleGraph W) (hH : H.CliqueFree 4)
    (f : oneGraph A →g H) : Nonempty (A ↪ Set ℕ) := by
  obtain ⟨c⟩ := two_pullback (R := fun a b : A => a < b) (fun a => lt_irrefl a)
    H hH (fun e => f (triple e)) (fun e d h => f.map_adj (triple_step e d h))
  exact ⟨⟨c,coloring_injective c⟩⟩

#print axioms first_index
#print axioms second_index
end Erdos595OrderedShiftTarget
