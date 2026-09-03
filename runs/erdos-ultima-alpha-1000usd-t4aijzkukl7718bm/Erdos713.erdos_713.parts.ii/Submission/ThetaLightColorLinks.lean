import FormalConjecturesUtil
import Submission.ThetaLightColoring
import Submission.ConditionalThetaWeighted

/-! A super-square-root degree would force high chromatic complexity in
EVERY row link's light graph. This does not exclude that complexity. -/
open Finset SimpleGraph
open scoped Classical
namespace Erdos713ThetaLightColorLinks
open Erdos713ThetaGram Erdos713GlobalLight Erdos713GlobalTheta
open Erdos713ConditionalThetaWeighted Erdos713ThetaHeavyShadow
set_option maxHeartbeats 2000000

def HasColoring {A B : Type*} (R : A → B → Prop) (r : ℕ) : Prop :=
  ∃ χ : B → Fin r, ∀ x y, x ≠ y → χ x = χ y → 3 ≤ codegree R x y

lemma colored_incidence_bound {A B : Type*} [Fintype A] [Fintype B]
    {R : A → B → Prop} {r : ℕ} (hf : ¬ HasTheta R) (hc : HasColoring R r) :
    (∑ a : A, (row R a).card) ≤ 3*r*Fintype.card A := by
  obtain ⟨χ,hχ⟩ := hc
  simpa only [Fintype.card_fin] using Erdos713ThetaLightColoring.incidences_le hf χ hχ

lemma degree_square_le {n d r : ℕ} (R : Fin n → Fin n → Prop) (a : Fin n)
    (hFree : pattern.Free (Erdos713C6.bipGraph R)) (hc : HasColoring (link R a) r)
    (hrows : ∀ a, d ≤ Nat.card {b // R a b})
    (hcols : ∀ b, d ≤ Nat.card {a // R a b}) : d^2 ≤ (3*r+1)*n := by
  let E := ∑ x : {x : Fin n // x ≠ a}, (row (link R a) x).card
  let M := Fintype.card {x : Fin n // x ≠ a}
  have hM : M ≤ n := by
    exact (Fintype.card_le_of_injective (fun x : {x : Fin n // x ≠ a} => x.val)
      Subtype.val_injective).trans_eq (Fintype.card_fin n)
  have hE : E ≤ 3*r*n :=
    (colored_incidence_bound (no_theta_links hFree a) hc).trans (Nat.mul_le_mul_left _ hM)
  have hLower : d*(d-1) ≤ E := by
    have hh := link_incidence_lower R a d (hrows a) hcols
    rw [Erdos713ThetaSplit.edge_card_eq_rows] at hh
    simpa only [E,row,Nat.card_eq_fintype_card,Fintype.card_subtype] using hh
  have hdn : d ≤ n := by
    apply (hrows a).trans
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
      (fun b : {b : Fin n // R a b} => b.val) Subtype.val_injective
  by_cases hd0 : d = 0
  · simp [hd0]
  have hsub : d-1+1 = d := Nat.sub_add_cancel (show 1 ≤ d by omega)
  nlinarith only [hE,hLower,hdn,hsub]

lemma no_bounded_coloring {n d r : ℕ} (R : Fin n → Fin n → Prop)
    (hFree : pattern.Free (Erdos713C6.bipGraph R))
    (hrows : ∀ a, d ≤ Nat.card {b // R a b})
    (hcols : ∀ b, d ≤ Nat.card {a // R a b}) (hd : (3*r+1)*n < d^2) :
    ∀ a : Fin n, ¬ HasColoring (link R a) r := by
  intro a hc
  exact (not_lt_of_ge (degree_square_le R a hFree hc hrows hcols)) hd

#print axioms colored_incidence_bound
#print axioms degree_square_le
#print axioms no_bounded_coloring
end Erdos713ThetaLightColorLinks
