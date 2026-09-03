import Submission.GreedyAmbientExtraction
import Submission.ControlledSquareDegrees
import Submission.PrioritySquareSidonLower

/-!
A square-Sidon extraction certificate combining penalized linearization,
maximum-degree trimming, and the unconditional bounded-degree greedy theorem.
The asymptotic numerical specialization is separate.
-/
namespace Erdos773.GreedySquareCertificate
open Finset Filter SquareCollisionCodegrees SquareCollisionIntersections
open SquareCollisionLinearization ControlledSquareLinearization ControlledSquareDegrees
open HypergraphDegreeTrim
set_option maxHeartbeats 2500000
noncomputable section

/-- Unlike the older coarse bound, the retained-edge term uses the actual
    edge count of the input carrier. -/
theorem finite_linearization {A : Finset ℕ}
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ)) (K : ℝ)
    (hK : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ((pairEdges A a b).card:ℝ) ≤ K)
    (p μ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hμ : 0 ≤ μ) :
    ∃ B ⊆ A, ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      LinearCollisions B ∧
      p*A.card-p^6*(A.card:ℝ)^2*K^2-μ*p^4*(edges A).card ≤ B.card-μ*(edges B).card := by
  classical
  have hcodeg (P : Finset ℕ) (hP : P ∈ A.powersetCard 2) :
      (((edges A).filter (fun e => P ⊆ e)).card:ℝ) ≤ K := by
    obtain ⟨hPA,hPc⟩ := mem_powersetCard.mp hP
    obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hPc
    have heq : (edges A).filter (fun e => ({a,b} : Finset ℕ) ⊆ e) = pairEdges A a b := by
      ext e
      simp [pairEdges,insert_subset_iff,singleton_subset_iff]
    rw [heq]
    exact hK a (hPA (by simp)) b (hPA (by simp)) hab
  obtain ⟨B,hBA,hlin,hcard⟩ := PenalizedAlteration.linearize A (edges A)
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    (fun e he => (mem_filter.mp he).2.1)
    (fun e he f hf hne => intersection_card_le_two hAP he hf hne)
    K hcodeg p μ hp hp1 hμ
  rw [← edges_restrict hBA] at hcard
  refine ⟨B,hBA,hAP.mono (by exact_mod_cast image_subset_image hBA),?_,hcard⟩
  intro e he f hf hne
  exact hlin e (edges_mono hBA he) (mem_powerset.mp (mem_filter.mp he).1)
    f (edges_mono hBA hf) (mem_powerset.mp (mem_filter.mp hf).1) hne

/-- The selected carrier pays for all overlap deletions and retained edges,
    and then loses at most half of its vertices to maximum-degree trimming. -/
theorem trimmed_linearization {A : Finset ℕ}
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ)) (K : ℝ)
    (hK : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ((pairEdges A a b).card:ℝ) ≤ K)
    (p μ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hμ : 0 < μ)
    (hoverlap : p^6*(A.card:ℝ)^2*K^2 ≤ p*A.card/4)
    (hedges : μ*p^4*(edges A).card ≤ p*A.card/4) :
    ∃ B ⊆ A, ThreeAPFree ((B.image (fun n : ℕ => n^2)) : Set ℕ) ∧
      LinearCollisions B ∧ p*A.card/4 ≤ (B.card:ℝ) ∧
      ∀ a ∈ B, (degree (edges B) a:ℝ) ≤ 8/μ := by
  classical
  obtain ⟨B,hBA,hBAP,hlin,hcost⟩ := finite_linearization hAP K hK p μ hp hp1 hμ.le
  have hlead : 0 ≤ p*(A.card:ℝ) := by positivity
  have hsurplus : p*A.card/2 ≤ (B.card:ℝ)-μ*(edges B).card := by
    linarith only [hcost,hoverlap,hedges]
  have hedge : ((edges B).card:ℝ) ≤ (1/μ)*(B.card:ℝ) := by
    rw [one_div,mul_comm,← div_eq_mul_inv]
    apply (le_div_iff₀ hμ).mpr
    have hh : μ*(edges B).card ≤ (B.card:ℝ) := by linarith only [hsurplus,hlead]
    simpa only [mul_comm] using hh
  obtain ⟨C,hCB,hCc,hCd⟩ := trim B (edges B)
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    (fun e he => (mem_filter.mp he).2.1) (1/μ) (by positivity) hedge
  have hCc' : (B.card:ℝ) ≤ 2*(C.card:ℝ) := by exact_mod_cast hCc
  have hnon : 0 ≤ μ*(edges B).card := by positivity
  refine ⟨C,hCB.trans hBA,hBAP.mono (by exact_mod_cast image_subset_image hCB),linear_mono hCB hlin,?_,?_⟩
  · linarith only [hsurplus,hCc',hnon]
  · intro a ha
    have hmono : (degree (edges C) a:ℝ) ≤ (degree (edges B) a:ℝ) := by
      exact_mod_cast degree_mono (edges_mono hCB) a
    have hh := hmono.trans (hCd a ha)
    simpa only [mul_one_div] using hh

/-- All process hypotheses have been discharged. What remains here is a
    finite list of carrier and scalar inequalities in the square problem. -/
theorem eventually_certificate (Aexp : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∀ᶠ m : ℕ in atTop, ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Icc 1 N → (N:ℝ) ≤ (m:ℝ)^Aexp →
      ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ) →
      ∀ K : ℝ, (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ((pairEdges A a b).card:ℝ) ≤ K) →
      ∀ p μ : ℝ, 0 ≤ p → p ≤ 1 → 0 < μ → 8/μ ≤ (m:ℝ)^12 →
      p^6*(A.card:ℝ)^2*K^2 ≤ p*A.card/4 → μ*p^4*(edges A).card ≤ p*A.card/4 →
      c*p*A.card/(4*(m:ℝ)^4) ≤
        (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ) := by
  classical
  filter_upwards [GreedyAmbientExtraction.eventually_selection (α := ℕ) Aexp c] with m hm
  intro N A hAN hNm hAP K hK p μ hp hp1 hμ hdegree hoverlap hedges
  obtain ⟨B,hBA,hBAP,hlin,hBcard,hBdegree⟩ := trimmed_linearization hAP K hK p μ hp hp1 hμ hoverlap hedges
  have hBN : B ⊆ Icc 1 N := hBA.trans hAN
  have hBupper : (B.card:ℝ) ≤ (m:ℝ)^Aexp := by
    have hh : B.card ≤ N := by simpa using card_le_card hBN
    exact (by exact_mod_cast hh : (B.card:ℝ) ≤ N).trans hNm
  have hdegrees : ∀ a ∈ B, degree (edges B) a ≤ m^12 := by
    intro a ha
    exact_mod_cast (hBdegree a ha).trans hdegree
  obtain ⟨I,hIB,hI,hIcard⟩ := hm B hBupper (edges B)
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    (fun e he => (mem_filter.mp he).2.1) hlin hdegrees
  have hsidon := PrioritySquareSidonLower.sidon_of_edge_avoidance hIB hBAP hI
  have hmax : (I.image (fun n : ℕ => n^2)).card ≤
      maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) :=
    le_sup (mem_filter.mpr ⟨mem_powerset.mpr (image_subset_image (hIB.trans hBN)),hsidon⟩)
  rw [card_image_of_injective I (Nat.pow_left_injective (by omega : (2:ℕ) ≠ 0))] at hmax
  have hscale := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hBcard hc)
    (pow_nonneg (Nat.cast_nonneg m) 4)
  have hscale' : c*p*A.card/(4*(m:ℝ)^4) ≤ c*B.card/(m:ℝ)^4 := by
    convert hscale using 1; ring
  exact hscale'.trans (hIcard.trans (by exact_mod_cast hmax))

#print axioms finite_linearization
#print axioms trimmed_linearization
#print axioms eventually_certificate
end
end Erdos773.GreedySquareCertificate
