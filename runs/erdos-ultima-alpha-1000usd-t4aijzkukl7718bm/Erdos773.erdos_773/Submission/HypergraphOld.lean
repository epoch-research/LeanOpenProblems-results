import FormalConjecturesUtil

/-! Finite alteration lemmas for the Sidon-subset problem. -/

namespace Erdos773

lemma delete_forbidden_edges {α : Type*} [DecidableEq α]
    (A : Finset α) (H : Finset (Finset α)) (hH : ∀ e ∈ H, e.Nonempty) :
    ∃ B ⊆ A, A.card ≤ B.card + H.card ∧ ∀ e ∈ H, ¬e ⊆ B := by
  classical
  induction H using Finset.induction_on with
  | empty => exact ⟨A, Finset.Subset.refl A, by simp, by simp⟩
  | @insert e H he ih =>
    obtain ⟨B, hBA, hcard, havoid⟩ := ih (fun f hf => hH f (Finset.mem_insert_of_mem hf))
    obtain ⟨a, ha⟩ := hH e (Finset.mem_insert_self e H)
    refine ⟨B.erase a, (Finset.erase_subset a B).trans hBA, ?_, ?_⟩
    · have hc : B.card ≤ (B.erase a).card + 1 := by
        by_cases hab : a ∈ B
        · rw [Finset.card_erase_of_mem hab]
          have : 0 < B.card := Finset.card_pos.mpr ⟨a, hab⟩
          omega
        · simp [Finset.erase_eq_of_notMem hab]
      rw [Finset.card_insert_of_notMem he]
      omega
    · intro f hf hfB
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact Finset.notMem_erase a B (hfB ha)
      · exact havoid f hf (hfB.trans (Finset.erase_subset a B))

section Bernoulli

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def trialWeight (p : ℝ) (f : α → Bool) : ℝ :=
  ∏ i, if f i then p else 1 - p

def selected (f : α → Bool) : Finset α := univ.filter (fun i => f i)

lemma trialWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (f : α → Bool) :
    0 ≤ trialWeight p f := by
  apply Finset.prod_nonneg
  intro i hi
  split <;> linarith

lemma sum_trialWeight (p : ℝ) : ∑ f : α → Bool, trialWeight p f = 1 := by
  unfold trialWeight
  rw [← Fintype.prod_sum (fun (_ : α) (b : Bool) => if b then p else 1 - p)]
  simp

lemma sum_trialWeight_contains (p : ℝ) (e : Finset α) :
    (∑ f : α → Bool, if e ⊆ selected f then trialWeight p f else 0) = p ^ e.card := by
  have hterm (f : α → Bool) :
      (if e ⊆ selected f then trialWeight p f else 0) =
        ∏ i, if i ∈ e then (if f i then p else 0) else (if f i then p else 1 - p) := by
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
    if i ∈ e then (if b then p else 0) else (if b then p else 1 - p))]
  simp [Fintype.sum_bool, Finset.prod_ite]

lemma sum_trialWeight_card (p : ℝ) :
    (∑ f : α → Bool, trialWeight p f * ((selected f).card : ℝ)) = p * Fintype.card α := by
  calc
    _ = ∑ f : α → Bool, ∑ i : α,
        if ({i} : Finset α) ⊆ selected f then trialWeight p f else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      simp [Finset.singleton_subset_iff, Finset.sum_ite_mem, mul_comm]
    _ = ∑ i : α, ∑ f : α → Bool,
        if ({i} : Finset α) ⊆ selected f then trialWeight p f else 0 := Finset.sum_comm
    _ = p * Fintype.card α := by
      simp_rw [sum_trialWeight_contains]
      simp [mul_comm]

lemma sum_trialWeight_edgeCount (p : ℝ) (H : Finset (Finset α)) :
    (∑ f : α → Bool, trialWeight p f * ((H.filter (· ⊆ selected f)).card : ℝ)) =
      ∑ e ∈ H, p ^ e.card := by
  calc
    _ = ∑ f : α → Bool, ∑ e ∈ H,
        if e ⊆ selected f then trialWeight p f else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      simp [← Finset.sum_filter, mul_comm]
    _ = ∑ e ∈ H, ∑ f : α → Bool,
        if e ⊆ selected f then trialWeight p f else 0 := Finset.sum_comm
    _ = ∑ e ∈ H, p ^ e.card := by simp_rw [sum_trialWeight_contains]

lemma alteration_bound (H : Finset (Finset α)) (hH : ∀ e ∈ H, e.Nonempty)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ B : Finset α, (∀ e ∈ H, ¬e ⊆ B) ∧
      p * Fintype.card α - (∑ e ∈ H, p ^ e.card) ≤ B.card := by
  let cost (f : α → Bool) : ℝ :=
    (selected f).card - (H.filter (· ⊆ selected f)).card
  obtain ⟨f, hf, hmax⟩ := Finset.exists_max_image Finset.univ cost Finset.univ_nonempty
  have hexpect : p * Fintype.card α - (∑ e ∈ H, p ^ e.card) ≤ cost f := by
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

noncomputable def sidonObstructions (A : Finset ℕ) : Finset (Finset A) :=
  Finset.univ.filter (fun e : Finset A => e.card ≤ 4 ∧
    ¬ IsSidon ((e.image (fun x : A => x.val) : Finset ℕ) : Set ℕ))

lemma sidonObstructions_nonempty (A : Finset ℕ) :
    ∀ e ∈ sidonObstructions A, e.Nonempty := by
  intro e he
  obtain ⟨_, _, hnot⟩ := Finset.mem_filter.mp he
  by_contra h
  have he : e = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  simp [he, IsSidon] at hnot

lemma sidon_of_avoids_obstructions (A : Finset ℕ) (B : Finset A)
    (hB : ∀ e ∈ sidonObstructions A, ¬e ⊆ B) :
    IsSidon ((B.image (fun x : A => x.val) : Finset ℕ) : Set ℕ) := by
  classical
  intro a ha b hb c hc d hd heq
  simp only [Finset.mem_coe, Finset.mem_image] at ha hb hc hd
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  obtain ⟨c, hc, rfl⟩ := hc
  obtain ⟨d, hd, rfl⟩ := hd
  by_contra hn
  let E : Finset A := {a, b, c, d}
  have hEcard : E.card ≤ 4 := by
    dsimp [E]
    have h1 := Finset.card_insert_le a {b, c, d}
    have h2 := Finset.card_insert_le b {c, d}
    have h3 := Finset.card_insert_le c {d}
    simp only [Finset.card_singleton] at h3
    omega
  have hEB : E ⊆ B := by
    intro x hx
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hEnot : ¬IsSidon ((E.image (fun x : A => x.val) : Finset ℕ) : Set ℕ) := by
    intro h
    apply hn
    apply h _ (by simp [E]) _ (by simp [E]) _ (by simp [E]) _ (by simp [E]) heq
  exact hB E (Finset.mem_filter.mpr ⟨Finset.mem_univ E, hEcard, hEnot⟩) hEB

lemma sidon_alteration_bound (A : Finset ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p * A.card - (∑ e ∈ sidonObstructions A, p ^ e.card) ≤
      (Finset.maxSidonSubsetCard A : ℝ) := by
  classical
  obtain ⟨B, hB, hcard⟩ := alteration_bound (sidonObstructions A)
    (sidonObstructions_nonempty A) p hp hp1
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
  simpa using hcard.trans (by exact_mod_cast hm)

#print axioms sidon_alteration_bound

end Erdos773
