import Submission.Hypergraph

/-!
Finite selection of a vertex subset on which a four-uniform hypergraph is
linear. This is an alteration lemma; no Sidon conclusion is asserted.
-/
namespace Erdos773.HypergraphLinearization
open Finset
set_option maxHeartbeats 1000000

variable {α : Type*} [DecidableEq α]

/-- Ambient-finset form of Bernoulli alteration. -/
theorem ambient_alteration (A : Finset α) (H : Finset (Finset α))
    (hsub : ∀ e ∈ H, e ⊆ A) (hn : ∀ e ∈ H, e.Nonempty)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ B ⊆ A, (∀ e ∈ H, ¬e ⊆ B) ∧
      p*A.card - (∑ e ∈ H, p^e.card) ≤ B.card := by
  classical
  let lift : Finset α → Finset A := Finset.subtype (fun a => a ∈ A)
  have hlift (e : Finset α) (he : e ⊆ A) : (lift e).map (Function.Embedding.subtype _) = e :=
    subtype_map_of_mem he
  have hlc (e : Finset α) (he : e ⊆ A) : (lift e).card = e.card := by
    calc
      _ = ((lift e).map (Function.Embedding.subtype _)).card := (card_map _).symm
      _ = e.card := by rw [hlift e he]
  have hli : Set.InjOn lift H := by
    intro e he f hf hh
    rw [← hlift e (hsub e he), ← hlift f (hsub f hf), hh]
  obtain ⟨B,hB,hcard⟩ := Erdos773.alteration_bound (H.image lift)
    (by
      intro e he
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      apply card_pos.mp
      rw [hlc f (hsub f hf)]
      exact card_pos.mpr (hn f hf)) p hp hp1
  let C := B.map (Function.Embedding.subtype _)
  have hCA : C ⊆ A := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := mem_map.mp ha
    exact b.property
  refine ⟨C,hCA,?_,?_⟩
  · intro e he heC
    apply hB (lift e) (mem_image.mpr ⟨e,he,rfl⟩)
    intro a ha
    have ha' : a.val ∈ e := mem_subtype.mp ha
    have hh := heC ha'
    obtain ⟨b,hb,heq⟩ := mem_map.mp hh
    have hba : b = a := Subtype.ext heq
    exact hba ▸ hb
  · have hcost : (∑ e ∈ H.image lift, p^e.card) = ∑ e ∈ H, p^e.card := by
      rw [sum_image hli]
      apply sum_congr rfl
      intro e he
      rw [hlc e (hsub e he)]
    rw [hcost, Fintype.card_coe] at hcard
    simpa only [C, card_map] using hcard

/-- Ordered pairs of distinct edges sharing at least two vertices. -/
def overlaps (H : Finset (Finset α)) : Finset (Finset α × Finset α) :=
  (H ×ˢ H).filter (fun ef => ef.1 ≠ ef.2 ∧ 2 ≤ (ef.1 ∩ ef.2).card)

/-- The six-vertex supports to delete. -/
def badSupports (H : Finset (Finset α)) : Finset (Finset α) :=
  (overlaps H).image (fun ef => ef.1 ∪ ef.2)

lemma badSupports_card_six {H : Finset (Finset α)}
    (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    {e : Finset α} (he : e ∈ badSupports H) : e.card = 6 := by
  obtain ⟨⟨f,g⟩,hfg,rfl⟩ := mem_image.mp he
  obtain ⟨hfg,hne,hge⟩ := mem_filter.mp hfg
  obtain ⟨hf,hg⟩ := mem_product.mp hfg
  change (f ∪ g).card = 6
  change 2 ≤ (f ∩ g).card at hge
  have hlo := h2 f hf g hg hne
  have hc := card_union_add_card_inter f g
  have hf4 := h4 f hf
  have hg4 := h4 g hg
  omega

lemma overlaps_cover {A : Finset α} {H : Finset (Finset α)}
    (hsub : ∀ e ∈ H, e ⊆ A) :
    overlaps H ⊆ (A.powersetCard 2).biUnion
      (fun P => (H.filter (fun e => P ⊆ e)) ×ˢ (H.filter (fun e => P ⊆ e))) := by
  intro ef hef
  obtain ⟨hef,hne,hge⟩ := mem_filter.mp hef
  obtain ⟨he,hf⟩ := mem_product.mp hef
  obtain ⟨P,hP,hPc⟩ := exists_subset_card_eq hge
  have hPe : P ⊆ ef.1 := hP.trans inter_subset_left
  have hPf : P ⊆ ef.2 := hP.trans inter_subset_right
  exact mem_biUnion.mpr ⟨P,mem_powersetCard.mpr ⟨hPe.trans (hsub _ he),hPc⟩,
    mem_product.mpr ⟨mem_filter.mpr ⟨he,hPe⟩,mem_filter.mpr ⟨hf,hPf⟩⟩⟩

/-- A two-vertex codegree bound controls all overlap supports. -/
theorem badSupports_count {A : Finset α} {H : Finset (Finset α)}
    (hsub : ∀ e ∈ H, e ⊆ A) (K : ℝ)
    (hcodeg : ∀ P ∈ A.powersetCard 2, ((H.filter (fun e => P ⊆ e)).card : ℝ) ≤ K) :
    ((badSupports H).card : ℝ) ≤ (A.card : ℝ)^2*K^2 := by
  have hc : (badSupports H).card ≤ ∑ P ∈ A.powersetCard 2,
      (H.filter (fun e => P ⊆ e)).card ^ 2 := by
    apply card_image_le.trans
    apply (card_le_card (overlaps_cover hsub)).trans
    simpa [card_product,pow_two] using (card_biUnion_le (s := A.powersetCard 2)
      (t := fun P => (H.filter (fun e => P ⊆ e)) ×ˢ (H.filter (fun e => P ⊆ e))))
  calc
    _ ≤ ∑ P ∈ A.powersetCard 2, ((H.filter (fun e => P ⊆ e)).card : ℝ)^2 := by exact_mod_cast hc
    _ ≤ ∑ _P ∈ A.powersetCard 2, K^2 := by
      apply sum_le_sum
      intro P hP
      exact pow_le_pow_left₀ (by positivity) (hcodeg P hP) 2
    _ = ((A.powersetCard 2).card : ℝ)*K^2 := by simp
    _ ≤ (A.card : ℝ)^2*K^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg K)
      exact_mod_cast (show (A.powersetCard 2).card ≤ A.card^2 by
        rw [card_powersetCard]; exact Nat.choose_le_pow _ _)

/-- An actual selected vertex set with pairwise edge intersections at most
one. Its finite lower bound follows by deleting six-vertex overlap supports. -/
theorem finite_selection (A : Finset α) (H : Finset (Finset α))
    (hsub : ∀ e ∈ H, e ⊆ A) (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (K : ℝ)
    (hcodeg : ∀ P ∈ A.powersetCard 2, ((H.filter (fun e => P ⊆ e)).card : ℝ) ≤ K)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ B ⊆ A,
      (∀ e ∈ H, e ⊆ B → ∀ f ∈ H, f ⊆ B → e ≠ f → (e ∩ f).card ≤ 1) ∧
      p*A.card - p^6*(A.card : ℝ)^2*K^2 ≤ B.card := by
  obtain ⟨B,hBA,hB,hcard⟩ := ambient_alteration A (badSupports H)
    (by
      intro e he
      obtain ⟨⟨f,g⟩,hfg,rfl⟩ := mem_image.mp he
      have hh := mem_product.mp (mem_filter.mp hfg).1
      exact union_subset (hsub _ hh.1) (hsub _ hh.2))
    (by
      intro e he
      apply card_pos.mp
      rw [badSupports_card_six h4 h2 he]
      norm_num) p hp hp1
  have hcost : (∑ e ∈ badSupports H, p^e.card) = p^6*(badSupports H).card := by
    calc
      _ = ∑ _e ∈ badSupports H, p^6 := by
        apply sum_congr rfl
        intro e he
        rw [badSupports_card_six h4 h2 he]
      _ = _ := by simp [mul_comm]
  rw [hcost] at hcard
  refine ⟨B,hBA,?_,?_⟩
  · intro e he heB f hf hfB hne
    by_contra! hh
    apply hB (e ∪ f)
    · exact mem_image.mpr ⟨(e,f),mem_filter.mpr ⟨mem_product.mpr ⟨he,hf⟩,hne,hh⟩,rfl⟩
    · exact union_subset heB hfB
  · have hc := badSupports_count hsub K hcodeg
    have hm := mul_le_mul_of_nonneg_left hc (pow_nonneg hp 6)
    nlinarith only [hcard,hm]

#print axioms ambient_alteration
#print axioms badSupports_count
#print axioms finite_selection
end Erdos773.HypergraphLinearization
