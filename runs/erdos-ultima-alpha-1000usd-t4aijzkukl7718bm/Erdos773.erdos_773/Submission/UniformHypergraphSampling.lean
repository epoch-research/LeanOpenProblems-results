import Submission.UniformDegreeSampling
import Submission.HypergraphDegreeTrim

/-! Uniform maximum-degree control under sampling of a four-uniform
hypergraph, simultaneously with deletion of three-vertex obstructions. -/
namespace Erdos773.UniformHypergraphSampling
open Finset HypergraphDegreeTrim
set_option maxHeartbeats 2000000
noncomputable section
variable {α : Type*} [DecidableEq α]

def link (H : Finset (Finset α)) (a : α) : Finset (Finset α) :=
  (H.filter (fun e => a ∈ e)).image (fun e => e.erase a)

lemma erase_injective (a : α) {H : Finset (Finset α)} :
    Set.InjOn (fun e : Finset α => e.erase a) (H.filter (fun e => a ∈ e)) := by
  intro e he f hf hh
  change e.erase a=f.erase a at hh
  rw [← insert_erase (mem_filter.mp he).2,← insert_erase (mem_filter.mp hf).2,hh]

lemma link_card (H : Finset (Finset α)) (a : α) : (link H a).card=degree H a := by
  unfold link degree
  exact card_image_of_injOn (erase_injective a)

lemma link_uniform {H : Finset (Finset α)} (hr : ∀ e ∈ H, e.card=4)
    (a : α) : ∀ e ∈ link H a, e.card=3 := by
  intro e he
  unfold link at he
  obtain ⟨f,hf,rfl⟩ := mem_image.mp he
  rw [card_erase_of_mem (mem_filter.mp hf).2,hr f (mem_filter.mp hf).1]

lemma link_degree (H : Finset (Finset α)) (a b : α) (K : ℕ)
    (hK : ∀ b, a ≠ b → (H.filter (fun e => a ∈ e ∧ b ∈ e)).card ≤ K) :
    ((link H a).filter (fun e => b ∈ e)).card ≤ K := by
  by_cases hab : a=b
  · subst b
    have he : (link H a).filter (fun e => a ∈ e)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨he,ha⟩ := mem_filter.mp he
      unfold link at he
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      exact notMem_erase a f ha
    rw [he,card_empty]
    omega
  · have hs : (link H a).filter (fun e => b ∈ e) ⊆
        (H.filter (fun e => a ∈ e ∧ b ∈ e)).image (fun e => e.erase a) := by
      intro e he
      obtain ⟨he,hb⟩ := mem_filter.mp he
      unfold link at he
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      exact mem_image.mpr ⟨f,mem_filter.mpr ⟨(mem_filter.mp hf).1,
        (mem_filter.mp hf).2,mem_of_mem_erase hb⟩,rfl⟩
    exact ((card_le_card hs).trans card_image_le).trans (hK b hab)

lemma induced_degree_le_link (H : Finset (Finset α)) (B : Finset α) (a : α) :
    degree (H.filter (· ⊆ B)) a ≤ ((link H a).filter (· ⊆ B)).card := by
  have hs : ((H.filter (· ⊆ B)).filter (fun e => a ∈ e)).image (fun e => e.erase a) ⊆
      (link H a).filter (· ⊆ B) := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    obtain ⟨hf,ha⟩ := mem_filter.mp hf
    obtain ⟨hf,hsub⟩ := mem_filter.mp hf
    exact mem_filter.mpr ⟨mem_image.mpr ⟨f,mem_filter.mpr ⟨hf,ha⟩,rfl⟩,
      (erase_subset _ _).trans hsub⟩
  have hh := card_le_card hs
  rw [card_image_of_injOn (erase_injective a)] at hh
  exact hh

variable [Fintype α]

/-- No average-degree trimming is performed. All surviving degrees meet
    the same cap T. -/
theorem finite_selection (H P : Finset (Finset α)) (K q : ℕ) (p T D : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hT : 0<T)
    (hfour : ∀ e ∈ H, e.card=4) (hthree : ∀ e ∈ P, e.card=3)
    (hdegree : ∀ a, (degree H a:ℝ) ≤ D)
    (hpair : ∀ a b, a ≠ b → (H.filter (fun e => a ∈ e ∧ b ∈ e)).card ≤ K)
    (hpositive : 0 < p*Fintype.card α-p^3*P.card-
      (Fintype.card α:ℝ)^2*((p^3*D+(3*q:ℕ)*K)/T)^q) :
    ∃ B : Finset α, (∀ e ∈ P, ¬e ⊆ B) ∧
      (∀ a, (degree (H.filter (· ⊆ B)) a:ℝ)<T) ∧
      p*Fintype.card α-p^3*P.card-
        (Fintype.card α:ℝ)^2*((p^3*D+(3*q:ℕ)*K)/T)^q ≤ (B.card:ℝ) := by
  obtain ⟨B,hP,hcap,hcard⟩ := UniformDegreeSampling.finite_selection (link H) P
    3 3 K q p T D hp hp1 hT (link_uniform hfour) (fun a b => link_degree H a b K (hpair a))
    (fun a => by rw [link_card]; exact hdegree a) hthree (by omega) (by simpa only [pow_two] using hpositive)
  refine ⟨B,hP,?_,?_⟩
  · intro a
    have hh : (degree (H.filter (· ⊆ B)) a:ℝ) ≤ ((link H a).filter (· ⊆ B)).card := by
      exact_mod_cast induced_degree_le_link H B a
    exact hh.trans_lt (hcap a)
  · simpa only [pow_two] using hcard

#print axioms link_card
#print axioms link_degree
#print axioms induced_degree_le_link
#print axioms finite_selection
end
end Erdos773.UniformHypergraphSampling
