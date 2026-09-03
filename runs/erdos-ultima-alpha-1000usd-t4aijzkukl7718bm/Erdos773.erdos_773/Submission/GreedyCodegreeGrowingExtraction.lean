import Submission.GreedyCodegreeGrowing
import Submission.GreedyAmbientExtraction

/-!
Removal of exact regularity by the verified polynomial-size regularization.
The independent-set density transfers with no further loss. Pair-codegree and intersection bounds are preserved.
-/
namespace Erdos773.GreedyCodegreeGrowingExtraction
open Finset Filter GreedyLinearDrift GreedyHypergraphState FourUniformRegularization
open GreedyPolynomialExtraction GreedyHorizonFactors
set_option maxHeartbeats 2500000
set_option exponentiation.threshold 10300
noncomputable section

/-- For every fixed polynomial volume bound, the extraction threshold is
    uniform over all horizons allowed by the explicit budget, including
    growing horizons. Regularization preserves the independent-set density. -/
theorem eventually_independent (A : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ τ : ℝ, 1 ≤ τ → horizonBudget τ ≤ (n:ℝ) →
      ∀ (α : Type*) [Fintype α] [DecidableEq α],
      (Fintype.card α:ℝ) ≤ (n:ℝ)^A →
      ∀ H : Finset (Finset α), (∀ e ∈ H, e.card = 4) →
      (∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2) →
      (∀ u : α, HypergraphDegreeTrim.degree H u ≤ n^300) →
      (∀ u v : α, u ≠ v → pairDegree H u v ≤ n^3) →
      ∃ I : Finset α, Independent H I ∧
        (Fintype.card α:ℝ)*τ/(2*(n:ℝ)^100) ≤ (I.card:ℝ) := by
  filter_upwards [GreedyCodegreeGrowing.eventually_independent (A+303),
    eventually_real_le_nat 2] with n hm hm2
  intro τ hτ hbudget α _ _ hVA H hfour hinter hdeg hcodeg
  by_cases hzero : Fintype.card α = 0
  · refine ⟨∅,?_,?_⟩
    · intro e he hsub
      have hh := card_le_card hsub
      rw [hfour e he,card_empty] at hh
      omega
    · simp only [hzero,Nat.cast_zero,zero_mul,zero_div,card_empty,le_refl]
  have hcardpos : (0:ℝ) < Fintype.card α := by exact_mod_cast Nat.pos_of_ne_zero hzero
  have hcardone : (1:ℝ) ≤ Fintype.card α := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
  have hmpos : (0:ℝ) < n := by linarith
  have hmone : (1:ℝ) ≤ n := by linarith
  have hm12 : (5:ℝ) ≤ (n:ℝ)^300 := by
    have hp := pow_le_pow_right₀ hmone (show 3 ≤ 300 by omega)
    have h8 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hm2 3
    norm_num at h8
    linarith only [hp,h8]
  have hm12n : 5 ≤ n^300 := by exact_mod_cast hm12
  obtain ⟨p,hprime,hpD,hp3,hpup,G,hGfour,hGreg,hGpair,hGinter,htransfer⟩ :=
    exists_regularization_prime H (n^300) (n^3) hfour hdeg
      (by exact_mod_cast one_le_pow₀ hmone (n := 3)) hcodeg
  letI : Fact p.Prime := ⟨hprime⟩
  have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
  have hplo : (n:ℝ)^300 ≤ p := by exact_mod_cast hpD
  have hpupper : (p:ℝ) ≤ 2*(n:ℝ)^300 := by
    have hh := hpup
    rw [max_eq_left hm12n] at hh
    exact_mod_cast hh
  have hGV : (Fintype.card (Vertex α (ZMod p)):ℝ) = 4*(p:ℝ)*(Fintype.card α:ℝ) := by
    simp only [vertex_card,ZMod.card,Nat.cast_mul,Nat.cast_ofNat]
  have hGlo : (n:ℝ)^300 ≤ (Fintype.card (Vertex α (ZMod p)):ℝ) := by
    rw [hGV]
    have hpv := mul_le_mul_of_nonneg_left hcardone hp0.le
    nlinarith only [hplo,hpv,hp0.le]
  have hGhi0 : (Fintype.card (Vertex α (ZMod p)):ℝ) ≤ (n:ℝ)^(A+303) := by
    rw [hGV]
    have h1 := mul_le_mul hpupper hVA hcardpos.le (by positivity : (0:ℝ) ≤ 2*(n:ℝ)^300)
    have h8 : (8:ℝ) ≤ (n:ℝ)^3 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hm2 3
      norm_num at hh
      exact hh
    have h2 := mul_le_mul_of_nonneg_right h8 (pow_nonneg hmpos.le (A+300))
    have he : (n:ℝ)^(A+303) = (n:ℝ)^A*(n:ℝ)^300*(n:ℝ)^3 := by
      rw [show A+303 = (A+300)+3 by omega,pow_add,pow_add]
    rw [he]
    rw [pow_add] at h2
    nlinarith only [h1,h2]
  have hGinter' := hGinter 2 (by omega) hinter
  obtain ⟨B,hB,hBcard⟩ := hm τ hτ hbudget (Vertex α (ZMod p)) hGlo hGhi0 G hGfour hGinter' hGreg hGpair
  obtain ⟨I,hI,hIcard⟩ := htransfer B hB
  refine ⟨I,hI,?_⟩
  have hIcard' : (B.card:ℝ) ≤ 4*(p:ℝ)*(I.card:ℝ) := by exact_mod_cast hIcard
  rw [hGV] at hBcard
  have hh : (4*(p:ℝ))*((Fintype.card α:ℝ)*τ/(2*(n:ℝ)^100)) ≤
      (4*(p:ℝ))*(I.card:ℝ) := by
    calc
      _ = (4*(p:ℝ)*(Fintype.card α:ℝ))*τ/(2*(n:ℝ)^100) := by ring
      _ ≤ (B.card:ℝ) := hBcard
      _ ≤ _ := hIcard'
  exact le_of_mul_le_mul_left hh (by positivity : (0:ℝ) < 4*(p:ℝ))

lemma pairDegree_lift {α : Type*} [DecidableEq α] {A : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e ∈ H, e ⊆ A) (x y : A) :
    pairDegree (GreedyAmbientExtraction.hypergraph A H) x y = pairDegree H x.val y.val := by
  have he : (GreedyAmbientExtraction.hypergraph A H).filter (fun e => x ∈ e ∧ y ∈ e) =
      (H.filter (fun e => x.val ∈ e ∧ y.val ∈ e)).image (GreedyAmbientExtraction.lift A) := by
    ext e
    simp only [GreedyAmbientExtraction.hypergraph,mem_filter,mem_image]
    constructor
    · rintro ⟨⟨f,hf,rfl⟩,hx,hy⟩
      exact ⟨f,⟨hf,mem_subtype.mp hx,mem_subtype.mp hy⟩,rfl⟩
    · rintro ⟨f,⟨hf,hx,hy⟩,rfl⟩
      exact ⟨⟨f,hf,rfl⟩,mem_subtype.mpr hx,mem_subtype.mpr hy⟩
  unfold pairDegree
  rw [he]
  exact card_image_of_injOn (GreedyAmbientExtraction.lift_injOn (fun e he => hH e (mem_filter.mp he).1))

lemma intersection_lift {α : Type*} [DecidableEq α] {A : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e ∈ H, e ⊆ A) (r : ℕ)
    (hinter : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ r) :
    ∀ e ∈ GreedyAmbientExtraction.hypergraph A H, ∀ f ∈ GreedyAmbientExtraction.hypergraph A H,
      e ≠ f → (e ∩ f).card ≤ r := by
  intro e he f hf hne
  obtain ⟨e,heH,rfl⟩ := mem_image.mp he
  obtain ⟨f,hfH,rfl⟩ := mem_image.mp hf
  have hne' : e ≠ f := fun hh => hne (hh ▸ rfl)
  have heq : ((GreedyAmbientExtraction.lift A e) ∩ (GreedyAmbientExtraction.lift A f)).map
      (Function.Embedding.subtype _) = e ∩ f := by
    rw [map_inter,GreedyAmbientExtraction.lift_map (hH e heH),GreedyAmbientExtraction.lift_map (hH f hfH)]
  rw [← card_map (Function.Embedding.subtype _),heq]
  exact hinter e heH f hfH hne'

/-- Arbitrary finite carriers, with the same growing horizon and no loss
    during subtype transport. -/
theorem eventually_selection {α : Type*} [DecidableEq α] (Aexp : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ τ : ℝ, 1 ≤ τ → horizonBudget τ ≤ (n:ℝ) →
      ∀ A : Finset α, (A.card:ℝ) ≤ (n:ℝ)^Aexp →
      ∀ H : Finset (Finset α), (∀ e ∈ H, e ⊆ A) → (∀ e ∈ H, e.card = 4) →
      (∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 2) →
      (∀ a ∈ A, HypergraphDegreeTrim.degree H a ≤ n^300) →
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → pairDegree H a b ≤ n^3) →
      ∃ I ⊆ A, (∀ e ∈ H, ¬e ⊆ I) ∧ (A.card:ℝ)*τ/(2*(n:ℝ)^100) ≤ (I.card:ℝ) := by
  filter_upwards [eventually_independent Aexp] with n hn
  intro τ hτ hbudget A hcard H hH hfour hinter hdeg hcodeg
  have hcard' : (Fintype.card A:ℝ) ≤ (n:ℝ)^Aexp := by simpa only [Fintype.card_coe] using hcard
  have hfour' : ∀ e ∈ GreedyAmbientExtraction.hypergraph A H, e.card = 4 := by
    intro e he
    obtain ⟨e,heH,rfl⟩ := mem_image.mp he
    rw [GreedyAmbientExtraction.lift_card (hH e heH),hfour e heH]
  have hdeg' : ∀ a : A, HypergraphDegreeTrim.degree (GreedyAmbientExtraction.hypergraph A H) a ≤ n^300 := by
    intro a
    rw [GreedyAmbientExtraction.degree_lift hH]
    exact hdeg a.val a.property
  obtain ⟨I,hI,hIc⟩ := hn τ hτ hbudget A hcard' (GreedyAmbientExtraction.hypergraph A H)
    hfour' (intersection_lift hH 2 hinter) hdeg' (fun a b hab => by
      rw [pairDegree_lift hH]
      exact hcodeg a.val a.property b.val b.property (fun h => hab (Subtype.ext h)))
  refine ⟨I.map (Function.Embedding.subtype _),?_,GreedyAmbientExtraction.project_independent hH hI,?_⟩
  · intro a ha
    obtain ⟨a,ha,rfl⟩ := mem_map.mp ha
    exact a.property
  · simpa only [card_map,Fintype.card_coe] using hIc

#print axioms eventually_independent
#print axioms eventually_selection
#print axioms pairDegree_lift
#print axioms intersection_lift
end
end Erdos773.GreedyCodegreeGrowingExtraction
