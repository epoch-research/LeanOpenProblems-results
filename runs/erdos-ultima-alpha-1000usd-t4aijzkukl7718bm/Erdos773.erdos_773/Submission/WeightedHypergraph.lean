import Submission.Hypergraph

/-! Finite independent selection with vertex-dependent probabilities. -/
namespace Erdos773.WeightedSelection

section Bernoulli

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def trialWeight (p : α → ℝ) (f : α → Bool) : ℝ :=
  ∏ i, if f i then p i else 1 - p i

def selected (f : α → Bool) : Finset α := univ.filter (fun i => f i)

omit [DecidableEq α] in
lemma trialWeight_nonneg {p : α → ℝ} (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (f : α → Bool) :
    0 ≤ trialWeight p f := by
  apply Finset.prod_nonneg
  intro i hi
  split <;> [exact hp i; exact sub_nonneg.mpr (hp1 i)]

lemma sum_trialWeight (p : α → ℝ) : ∑ f : α → Bool, trialWeight p f = 1 := by
  unfold trialWeight
  rw [← Fintype.prod_sum (fun (i : α) (b : Bool) => if b then p i else 1 - p i)]
  simp

lemma sum_trialWeight_contains (p : α → ℝ) (e : Finset α) :
    (∑ f : α → Bool, if e ⊆ selected f then trialWeight p f else 0) = (∏ i ∈ e, p i) := by
  have hterm (f : α → Bool) :
      (if e ⊆ selected f then trialWeight p f else 0) =
        ∏ i, if i ∈ e then (if f i then p i else 0) else (if f i then p i else 1 - p i) := by
    by_cases h : e ⊆ selected f
    · rw [if_pos h]
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hie : i ∈ e
      · have hf : f i = true := by simpa [selected] using h hie
        simp [hie, hf]
      · simp [hie]
    · rw [if_neg h]
      obtain ⟨i, hie, hi⟩ := Finset.not_subset.mp h
      have hf : f i = false := by simpa [selected] using hi
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hie, hf]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun (i : α) (b : Bool) =>
    if i ∈ e then (if b then p i else 0) else (if b then p i else 1 - p i))]
  simp

lemma sum_trialWeight_card (p : α → ℝ) :
    (∑ f : α → Bool, trialWeight p f * ((selected f).card : ℝ)) = (∑ i : α, p i) := by
  calc
    _ = ∑ f : α → Bool, ∑ i : α,
        if ({i} : Finset α) ⊆ selected f then trialWeight p f else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      simp [Finset.singleton_subset_iff, Finset.sum_ite_mem, mul_comm]
    _ = ∑ i : α, ∑ f : α → Bool,
        if ({i} : Finset α) ⊆ selected f then trialWeight p f else 0 := Finset.sum_comm
    _ = (∑ i : α, p i) := by
      simp_rw [sum_trialWeight_contains]
      simp

lemma sum_trialWeight_edgeCount (p : α → ℝ) (H : Finset (Finset α)) :
    (∑ f : α → Bool, trialWeight p f * ((H.filter (· ⊆ selected f)).card : ℝ)) =
      ∑ e ∈ H, (∏ i ∈ e, p i) := by
  calc
    _ = ∑ f : α → Bool, ∑ e ∈ H,
        if e ⊆ selected f then trialWeight p f else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      simp [← Finset.sum_filter, mul_comm]
    _ = ∑ e ∈ H, ∑ f : α → Bool,
        if e ⊆ selected f then trialWeight p f else 0 := Finset.sum_comm
    _ = ∑ e ∈ H, (∏ i ∈ e, p i) := by simp_rw [sum_trialWeight_contains]

lemma alteration_bound (H : Finset (Finset α)) (hH : ∀ e ∈ H, e.Nonempty)
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    ∃ B : Finset α, (∀ e ∈ H, ¬e ⊆ B) ∧
      (∑ i : α, p i) - (∑ e ∈ H, (∏ i ∈ e, p i)) ≤ B.card := by
  let cost (f : α → Bool) : ℝ :=
    (selected f).card - (H.filter (· ⊆ selected f)).card
  obtain ⟨f, hf, hmax⟩ := Finset.exists_max_image Finset.univ cost Finset.univ_nonempty
  have hexpect : (∑ i : α, p i) - (∑ e ∈ H, (∏ i ∈ e, p i)) ≤ cost f := by
    have hle : (∑ g : α → Bool, trialWeight p g * cost g) ≤
        ∑ g : α → Bool, trialWeight p g * cost f := by
      apply Finset.sum_le_sum
      intro g hg
      exact mul_le_mul_of_nonneg_left (hmax g hg) (trialWeight_nonneg hp hp1 g)
    simpa only [cost, mul_sub, Finset.sum_sub_distrib, sum_trialWeight_card,
      sum_trialWeight_edgeCount, ← Finset.sum_mul, sum_trialWeight, one_mul] using hle
  obtain ⟨B, hB, hcard, havoid⟩ := delete_forbidden_edges (selected f)
    (H.filter (· ⊆ selected f)) (fun e he => hH e (Finset.mem_filter.mp he).1)
  refine ⟨B, ?_, hexpect.trans ?_⟩
  · intro e he heB
    exact havoid e (Finset.mem_filter.mpr ⟨he, heB.trans hB⟩) heB
  · have hcard' : ((selected f).card : ℝ) ≤
        B.card + (H.filter (· ⊆ selected f)).card := by exact_mod_cast hcard
    dsimp [cost]
    linarith

end Bernoulli

lemma sidon_alteration_bound (A : Finset ℕ) (p : ℕ → ℝ)
    (hp : ∀ a ∈ A, 0 ≤ p a) (hp1 : ∀ a ∈ A, p a ≤ 1) :
    (∑ a ∈ A, p a) - (∑ e ∈ sidonObstructions A, (∏ a ∈ e, p a.val)) ≤
      (Finset.maxSidonSubsetCard A : ℝ) := by
  classical
  obtain ⟨B, hB, hcard⟩ := alteration_bound (sidonObstructions A)
    (sidonObstructions_nonempty A) (fun a : A => p a.val)
      (fun a => hp a.val a.property) (fun a => hp1 a.val a.property)
  have hsidon := sidon_of_avoids_obstructions A B hB
  have hsub : B.image (fun x : A => x.val) ⊆ A := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact a.property
  have hm : (B.image (fun x : A => x.val)).card ≤ Finset.maxSidonSubsetCard A :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hsidon⟩)
  have hBi : (B.image (fun x : A => x.val)).card = B.card :=
    Finset.card_image_of_injective B Subtype.val_injective
  rw [hBi] at hm
  simpa only [Finset.sum_coe_sort] using hcard.trans (by exact_mod_cast hm)


#print axioms sidon_alteration_bound
end Erdos773.WeightedSelection
