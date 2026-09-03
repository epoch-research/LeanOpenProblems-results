import Submission.UniformHypergraphSampling
import Submission.FiniteHypergraphRestriction

/-! Transport of uniform sampling to arbitrary finite ambient carriers. -/
namespace Erdos773.UniformAmbientSampling
open Finset HypergraphDegreeTrim FiniteHypergraphRestriction
set_option maxHeartbeats 2000000
noncomputable section
variable {α : Type*} [DecidableEq α]

/-- The finite carrier is arbitrary; no global Fintype structure is needed. -/
theorem finite_selection (A : Finset α) (H P : Finset (Finset α)) (K q : ℕ) (p T D : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hT : 0<T)
    (hH : ∀ e ∈ H, e ⊆ A) (hP : ∀ e ∈ P, e ⊆ A)
    (hfour : ∀ e ∈ H, e.card=4) (hthree : ∀ e ∈ P, e.card=3)
    (hdegree : ∀ a ∈ A, (degree H a:ℝ) ≤ D)
    (hpair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (H.filter (fun e => a ∈ e ∧ b ∈ e)).card ≤ K)
    (hpositive : 0 < p*A.card-p^3*P.card-(A.card:ℝ)^2*((p^3*D+(3*q:ℕ)*K)/T)^q) :
    ∃ B ⊆ A, (∀ e ∈ P, ¬e ⊆ B) ∧
      (∀ a ∈ A, (degree (H.filter (· ⊆ B)) a:ℝ)<T) ∧
      p*A.card-p^3*P.card-(A.card:ℝ)^2*((p^3*D+(3*q:ℕ)*K)/T)^q ≤ (B.card:ℝ) := by
  have hPcard : (restrict A P).card=P.card := restrict_card hP
  obtain ⟨I,hI,hcap,hcard⟩ := UniformHypergraphSampling.finite_selection
    (restrict A H) (restrict A P) K q p T D hp hp1 hT
    (by
      intro e he
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      rw [down_card (hH f hf),hfour f hf])
    (by
      intro e he
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      rw [down_card (hP f hf),hthree f hf])
    (by intro a; rw [degree_all_eq hH]; exact hdegree a.val a.property)
    (by
      intro a b hab
      change FourUniformRegularization.pairDegree (restrict A H) a b ≤ K
      rw [pair_eq hH]
      exact hpair a.val a.property b.val b.property (fun h => hab (Subtype.ext h)))
    (by simpa only [Fintype.card_coe,hPcard] using hpositive)
  refine ⟨up A I,?_,(independent_iff hP I).mp hI,?_,?_⟩
  · exact up_subset I
  · intro a ha
    have hh := hcap ⟨a,ha⟩
    rw [restrict_induced hH,degree_all_eq (fun e he => hH e (mem_filter.mp he).1)] at hh
    exact hh
  · simpa only [up_card,Fintype.card_coe,hPcard] using hcard

#print axioms finite_selection
end
end Erdos773.UniformAmbientSampling
