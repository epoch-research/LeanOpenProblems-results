import Submission.GreedyBoundedDegreeExtraction

/-!
Ambient-finset versions of the unconditional greedy extraction theorem.
All hypergraph, degree, and independence data are transported exactly to
and from the finite carrier type.
-/
namespace Erdos773.GreedyAmbientExtraction
open Finset Filter GreedyLinearDrift GreedyHypergraphState HypergraphDegreeTrim
open GreedyPolynomialExtraction
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [DecidableEq α]

def lift (A : Finset α) (e : Finset α) : Finset A := e.subtype (fun a => a ∈ A)
def hypergraph (A : Finset α) (H : Finset (Finset α)) : Finset (Finset A) := H.image (lift A)

lemma lift_map {A e : Finset α} (he : e ⊆ A) :
    (lift A e).map (Function.Embedding.subtype _) = e := subtype_map_of_mem he

lemma lift_card {A e : Finset α} (he : e ⊆ A) : (lift A e).card = e.card := by
  rw [← card_map (Function.Embedding.subtype _),lift_map he]

lemma lift_injOn {A : Finset α} {H : Finset (Finset α)} (hH : ∀ e ∈ H, e ⊆ A) :
    Set.InjOn (lift A) H := by
  intro e he f hf hh
  rw [← lift_map (hH e he),← lift_map (hH f hf),hh]

lemma degree_lift {A : Finset α} {H : Finset (Finset α)} (hH : ∀ e ∈ H, e ⊆ A) (x : A) :
    degree (hypergraph A H) x = degree H x.val := by
  have he : (hypergraph A H).filter (fun e => x ∈ e) =
      (H.filter (fun e => x.val ∈ e)).image (lift A) := by
    ext e
    simp only [hypergraph,mem_filter,mem_image]
    constructor
    · rintro ⟨⟨f,hf,rfl⟩,hx⟩
      exact ⟨f,⟨hf,mem_subtype.mp hx⟩,rfl⟩
    · rintro ⟨f,⟨hf,hx⟩,rfl⟩
      exact ⟨⟨f,hf,rfl⟩,mem_subtype.mpr hx⟩
  unfold degree
  rw [he]
  exact card_image_of_injOn (lift_injOn (fun e he => hH e (mem_filter.mp he).1))

lemma linear_lift {A : Finset α} {H : Finset (Finset α)} (hH : ∀ e ∈ H, e ⊆ A)
    (hlin : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 1) : Linear (hypergraph A H) := by
  intro e he f hf hne
  obtain ⟨e,heH,rfl⟩ := mem_image.mp he
  obtain ⟨f,hfH,rfl⟩ := mem_image.mp hf
  have hne' : e ≠ f := fun hh => hne (hh ▸ rfl)
  have heq : ((lift A e) ∩ (lift A f)).map (Function.Embedding.subtype _) = e ∩ f := by
    rw [map_inter,lift_map (hH e heH),lift_map (hH f hfH)]
  rw [← card_map (Function.Embedding.subtype _),heq]
  exact hlin e heH f hfH hne'

lemma project_independent {A : Finset α} {H : Finset (Finset α)} (hH : ∀ e ∈ H, e ⊆ A)
    {I : Finset A} (hI : Independent (hypergraph A H) I) :
    ∀ e ∈ H, ¬e ⊆ I.map (Function.Embedding.subtype _) := by
  intro e he hsub
  apply hI (lift A e) (mem_image.mpr ⟨e,he,rfl⟩)
  apply map_subset_map.mp
  rwa [lift_map (hH e he)]

/-- Finite carriers need not exhaust the ambient type. The result is still
    uniform in the carrier and in every four-uniform linear hypergraph on it. -/
theorem eventually_selection (Aexp : ℕ) (c : ℝ) :
    ∀ᶠ m : ℕ in atTop, ∀ A : Finset α, (A.card:ℝ) ≤ (m:ℝ)^Aexp →
      ∀ H : Finset (Finset α), (∀ e ∈ H, e ⊆ A) → (∀ e ∈ H, e.card = 4) →
      (∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 1) →
      (∀ a ∈ A, degree H a ≤ m^12) →
      ∃ I ⊆ A, (∀ e ∈ H, ¬e ⊆ I) ∧ c*(A.card:ℝ)/(m:ℝ)^4 ≤ (I.card:ℝ) := by
  filter_upwards [GreedyBoundedDegreeExtraction.eventually_arbitrary_multiplier Aexp c] with m hm
  intro A hcard H hH hfour hlin hdeg
  have hcard' : (Fintype.card A:ℝ) ≤ (m:ℝ)^Aexp := by simpa only [Fintype.card_coe] using hcard
  have hfour' : ∀ e ∈ hypergraph A H, e.card = 4 := by
    intro e he
    obtain ⟨e,heH,rfl⟩ := mem_image.mp he
    rw [lift_card (hH e heH),hfour e heH]
  have hdeg' : ∀ a : A, degree (hypergraph A H) a ≤ m^12 := by
    intro a
    rw [degree_lift hH]
    exact hdeg a.val a.property
  obtain ⟨I,hI,hIc⟩ := hm A hcard' (hypergraph A H) (linear_lift hH hlin) hfour' hdeg'
  refine ⟨I.map (Function.Embedding.subtype _),?_,project_independent hH hI,?_⟩
  · intro a ha
    obtain ⟨a,ha,rfl⟩ := mem_map.mp ha
    exact a.property
  · simpa only [card_map,Fintype.card_coe] using hIc

#print axioms degree_lift
#print axioms linear_lift
#print axioms eventually_selection
end
end Erdos773.GreedyAmbientExtraction
