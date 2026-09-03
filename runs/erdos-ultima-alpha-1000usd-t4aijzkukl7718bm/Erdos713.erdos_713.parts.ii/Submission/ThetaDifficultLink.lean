import FormalConjecturesUtil
import Submission.ThetaClusterLinks
import Submission.ThetaLightColorLinks

/-! The SAME selected punctured link carries the numerical bounds and both
structural obstructions. This is a necessary condition, not a contradiction. -/
open Finset SimpleGraph
open scoped Classical
namespace Erdos713ThetaDifficultLink
open Erdos713GlobalLight Erdos713GlobalTheta Erdos713ThetaGram
open Erdos713ConditionalThetaWeighted Erdos713ThetaHeavyShadow Erdos713ThetaCross
open Erdos713ThetaCluster Erdos713ThetaLightColorLinks
set_option maxHeartbeats 2000000

lemma exists_difficult_link {n d : ℕ} (hn : 0 < n) (R : Fin n → Fin n → Prop)
    (hFree : pattern.Free (Erdos713C6.bipGraph R))
    (hrows : ∀ a, d ≤ Nat.card {b // R a b})
    (hcols : ∀ b, d ≤ Nat.card {a // R a b}) :
    ∃ a : Fin n,
      ¬ HasTheta (link R a) ∧
      lightCount (link R a) ≤ 3*n ∧
      d*(d-1) ≤ ∑ x : {x : Fin n // x ≠ a}, (row (link R a) x).card ∧
      (∀ r : ℕ, (3*r+1)*n < d^2 → ¬ HasColoring (link R a) r) ∧
      (11*n < d^2 → ¬ ∃ τ : {b : Fin n // R a b} → ℕ,
        CrossHeavy (link R a) τ ∧ SameLight (link R a) τ) := by
  haveI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨a,ha⟩ := exists_row_with_few_light_pairs R 3
  simp only [Fintype.card_fin] at ha
  have ht : (lightPairs R 3 a).card ≤ 3*n := by
    have ht' : n*(lightPairs R 3 a).card ≤ n*(3*n) := by nlinarith only [ha]
    exact Nat.le_of_mul_le_mul_left ht' hn
  have ht' : lightCount (link R a) ≤ 3*n := by rw [link_lightCount]; exact ht
  have hLower : d*(d-1) ≤ ∑ x : {x : Fin n // x ≠ a}, (row (link R a) x).card := by
    have hh := link_incidence_lower R a d (hrows a) hcols
    rw [Erdos713ThetaSplit.edge_card_eq_rows] at hh
    simpa only [row,Nat.card_eq_fintype_card,Fintype.card_subtype] using hh
  refine ⟨a,no_theta_links hFree a,ht',hLower,?_,?_⟩
  · intro r hr
    exact no_bounded_coloring R hFree hrows hcols hr a
  · rintro hd ⟨τ,hH,hL⟩
    exact (not_lt_of_ge (Erdos713ThetaClusterLinks.degree_of_selected R a
      hFree τ hH hL ht' hrows hcols)) hd

#print axioms exists_difficult_link
end Erdos713ThetaDifficultLink
