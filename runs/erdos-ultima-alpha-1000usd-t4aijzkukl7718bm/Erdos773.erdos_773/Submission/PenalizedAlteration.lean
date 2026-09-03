import Submission.HypergraphLinearization

/-!
Bernoulli alteration with a retained-edge penalty. This permits simultaneous
control of selected cardinality and the number of surviving collision edges.
-/
namespace Erdos773.PenalizedAlteration
open Finset
set_option maxHeartbeats 1000000

variable {α : Type*} [DecidableEq α]

section Finite
variable [Fintype α]

theorem alteration (H G : Finset (Finset α)) (hH : ∀ e ∈ H, e.Nonempty)
    (p μ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hμ : 0 ≤ μ) :
    ∃ B : Finset α, (∀ e ∈ H, ¬e ⊆ B) ∧
      p*Fintype.card α - (∑ e ∈ H, p^e.card) - μ*(∑ e ∈ G, p^e.card) ≤
        B.card - μ*(G.filter (fun e => e ⊆ B)).card := by
  classical
  let cost (f : α → Bool) : ℝ :=
    (Erdos773.selected f).card - (H.filter (fun e => e ⊆ Erdos773.selected f)).card -
      μ*(G.filter (fun e => e ⊆ Erdos773.selected f)).card
  obtain ⟨f,hf,hmax⟩ := exists_max_image univ cost univ_nonempty
  have havg : p*Fintype.card α - (∑ e ∈ H, p^e.card) - μ*(∑ e ∈ G, p^e.card) ≤ cost f := by
    have hh : (∑ g : α → Bool, Erdos773.trialWeight p g * cost g) ≤
        ∑ g : α → Bool, Erdos773.trialWeight p g * cost f := by
      apply sum_le_sum
      intro g hg
      exact mul_le_mul_of_nonneg_left (hmax g hg) (Erdos773.trialWeight_nonneg hp hp1 g)
    have hweighted (g : α → Bool) : Erdos773.trialWeight p g * cost g =
        Erdos773.trialWeight p g * (Erdos773.selected g).card -
        Erdos773.trialWeight p g * (H.filter (fun e => e ⊆ Erdos773.selected g)).card -
        μ*(Erdos773.trialWeight p g * (G.filter (fun e => e ⊆ Erdos773.selected g)).card) := by
      dsimp [cost]
      ring
    simp_rw [hweighted] at hh
    simpa only [sum_sub_distrib, ← mul_sum, Erdos773.sum_trialWeight_card,
      Erdos773.sum_trialWeight_edgeCount, ← sum_mul, Erdos773.sum_trialWeight, one_mul] using hh
  obtain ⟨B,hB,hcard,havoid⟩ := Erdos773.delete_forbidden_edges (Erdos773.selected f)
    (H.filter (fun e => e ⊆ Erdos773.selected f)) (fun e he => hH e (mem_filter.mp he).1)
  refine ⟨B,?_,havg.trans ?_⟩
  · intro e he heB
    exact havoid e (mem_filter.mpr ⟨he,heB.trans hB⟩) heB
  · have hcount : ((G.filter (fun e => e ⊆ B)).card : ℝ) ≤
        (G.filter (fun e => e ⊆ Erdos773.selected f)).card := by
      exact_mod_cast card_le_card (show G.filter (fun e => e ⊆ B) ⊆
        G.filter (fun e => e ⊆ Erdos773.selected f) from fun e he =>
          mem_filter.mpr ⟨(mem_filter.mp he).1,(mem_filter.mp he).2.trans hB⟩)
    have hmul := mul_le_mul_of_nonneg_left hcount hμ
    have hc : ((Erdos773.selected f).card : ℝ) ≤
        B.card + (H.filter (fun e => e ⊆ Erdos773.selected f)).card := by exact_mod_cast hcard
    dsimp [cost]
    linarith
end Finite

/-- Ambient-finset version, with both forbidden and penalized edge families. -/
theorem ambient (A : Finset α) (H G : Finset (Finset α))
    (hH : ∀ e ∈ H, e ⊆ A) (hG : ∀ e ∈ G, e ⊆ A)
    (hn : ∀ e ∈ H, e.Nonempty)
    (p μ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hμ : 0 ≤ μ) :
    ∃ B ⊆ A, (∀ e ∈ H, ¬e ⊆ B) ∧
      p*A.card - (∑ e ∈ H, p^e.card) - μ*(∑ e ∈ G, p^e.card) ≤
        B.card - μ*(G.filter (fun e => e ⊆ B)).card := by
  classical
  let lift : Finset α → Finset A := Finset.subtype (fun a => a ∈ A)
  have hlift (e : Finset α) (he : e ⊆ A) : (lift e).map (Function.Embedding.subtype _) = e :=
    subtype_map_of_mem he
  have hlc (e : Finset α) (he : e ⊆ A) : (lift e).card = e.card := by
    calc
      _ = ((lift e).map (Function.Embedding.subtype _)).card := (card_map _).symm
      _ = e.card := by rw [hlift e he]
  have hli {F : Finset (Finset α)} (hF : ∀ e ∈ F, e ⊆ A) : Set.InjOn lift F := by
    intro e he f hf hh
    rw [← hlift e (hF e he), ← hlift f (hF f hf), hh]
  obtain ⟨B,hB,hcard⟩ := alteration (H.image lift) (G.image lift)
    (by
      intro e he
      obtain ⟨f,hf,rfl⟩ := mem_image.mp he
      apply card_pos.mp
      rw [hlc f (hH f hf)]
      exact card_pos.mpr (hn f hf)) p μ hp hp1 hμ
  let C := B.map (Function.Embedding.subtype _)
  have hCA : C ⊆ A := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := mem_map.mp ha
    exact b.property
  have hlsub (e : Finset α) (he : e ⊆ A) : lift e ⊆ B ↔ e ⊆ C := by
    calc
      _ ↔ (lift e).map (Function.Embedding.subtype _) ⊆ B.map (Function.Embedding.subtype _) :=
        map_subset_map.symm
      _ ↔ _ := by rw [hlift e he]
  have hcost {F : Finset (Finset α)} (hF : ∀ e ∈ F, e ⊆ A) :
      (∑ e ∈ F.image lift, p^e.card) = ∑ e ∈ F, p^e.card := by
    rw [sum_image (hli hF)]
    apply sum_congr rfl
    intro e he
    rw [hlc e (hF e he)]
  have hfilter : (G.image lift).filter (fun e => e ⊆ B) =
      (G.filter (fun e => e ⊆ C)).image lift := by
    ext e
    simp only [mem_filter,mem_image]
    constructor
    · rintro ⟨⟨f,hf,rfl⟩,hfe⟩
      exact ⟨f,⟨hf,(hlsub f (hG f hf)).mp hfe⟩,rfl⟩
    · rintro ⟨f,⟨hf,hfC⟩,rfl⟩
      exact ⟨⟨f,hf,rfl⟩,(hlsub f (hG f hf)).mpr hfC⟩
  have hfc : ((G.image lift).filter (fun e => e ⊆ B)).card =
      (G.filter (fun e => e ⊆ C)).card := by
    rw [hfilter]
    exact card_image_of_injOn (hli (fun e he => hG e (mem_filter.mp he).1))
  refine ⟨C,hCA,?_,?_⟩
  · intro e he heC
    exact hB (lift e) (mem_image.mpr ⟨e,he,rfl⟩) ((hlsub e (hH e he)).mpr heC)
  · rw [hcost hH,hcost hG,hfc,Fintype.card_coe] at hcard
    simpa only [C,card_map] using hcard

/-- Simultaneous linearization and retained-edge control. -/
theorem linearize (A : Finset α) (H : Finset (Finset α))
    (hsub : ∀ e ∈ H, e ⊆ A) (h4 : ∀ e ∈ H, e.card = 4)
    (h2 : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2)
    (K : ℝ)
    (hcodeg : ∀ P ∈ A.powersetCard 2, ((H.filter (fun e => P ⊆ e)).card : ℝ) ≤ K)
    (p μ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hμ : 0 ≤ μ) :
    ∃ B ⊆ A,
      (∀ e ∈ H, e ⊆ B → ∀ f ∈ H, f ⊆ B → e ≠ f → (e ∩ f).card ≤ 1) ∧
      p*A.card - p^6*(A.card : ℝ)^2*K^2 - μ*p^4*H.card ≤
        B.card - μ*(H.filter (fun e => e ⊆ B)).card := by
  classical
  let bad := HypergraphLinearization.badSupports H
  have hbad (e : Finset α) (he : e ∈ bad) : e.card = 6 :=
    HypergraphLinearization.badSupports_card_six h4 h2 he
  obtain ⟨B,hBA,hB,hcard⟩ := ambient A bad H
    (by
      intro e he
      obtain ⟨⟨f,g⟩,hfg,rfl⟩ := mem_image.mp he
      have hh := mem_product.mp (mem_filter.mp hfg).1
      exact union_subset (hsub _ hh.1) (hsub _ hh.2)) hsub
    (fun e he => card_pos.mp (by rw [hbad e he]; norm_num)) p μ hp hp1 hμ
  have hc (F : Finset (Finset α)) (k : ℕ) (hF : ∀ e ∈ F, e.card = k) :
      (∑ e ∈ F, p^e.card) = p^k*F.card := by
    calc
      _ = ∑ _e ∈ F, p^k := by apply sum_congr rfl; intro e he; rw [hF e he]
      _ = _ := by simp [mul_comm]
  rw [hc bad 6 hbad,hc H 4 h4] at hcard
  refine ⟨B,hBA,?_,?_⟩
  · intro e he heB f hf hfB hne
    by_contra! hh
    apply hB (e ∪ f)
    · exact mem_image.mpr ⟨(e,f),mem_filter.mpr ⟨mem_product.mpr ⟨he,hf⟩,hne,hh⟩,rfl⟩
    · exact union_subset heB hfB
  · have hcount := HypergraphLinearization.badSupports_count hsub K hcodeg
    have hm := mul_le_mul_of_nonneg_left hcount (pow_nonneg hp 6)
    change ((bad).card : ℝ) ≤ _ at hcount
    nlinarith only [hcard,hm]

#print axioms alteration
#print axioms ambient
#print axioms linearize
end Erdos773.PenalizedAlteration
