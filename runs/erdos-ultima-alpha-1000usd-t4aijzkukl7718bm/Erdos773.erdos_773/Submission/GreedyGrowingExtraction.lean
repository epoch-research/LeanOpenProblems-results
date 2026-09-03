import Submission.GreedyGrowingFailure
import Submission.GreedyAmbientExtraction

/-!
Removal of exact regularity by the verified polynomial-size regularization.
The independent-set density transfers with no further loss.
-/
namespace Erdos773.GreedyGrowingExtraction
open Finset Filter GreedyLinearDrift GreedyHypergraphState FourUniformRegularization
open GreedyPolynomialExtraction GreedyHorizonFactors
set_option maxHeartbeats 2500000
noncomputable section

/-- For every fixed polynomial volume bound, the extraction threshold is
    uniform over all horizons allowed by the explicit budget, including
    growing horizons. Regularization preserves the independent-set density. -/
theorem eventually_independent (A : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ τ : ℝ, 1 ≤ τ → horizonBudget τ ≤ (n:ℝ) →
      ∀ (α : Type*) [Fintype α] [DecidableEq α],
      (Fintype.card α:ℝ) ≤ (n:ℝ)^A →
      ∀ H : Finset (Finset α), Linear H → (∀ e ∈ H, e.card = 4) →
      (∀ u : α, HypergraphDegreeTrim.degree H u ≤ n^24) →
      ∃ I : Finset α, Independent H I ∧
        (Fintype.card α:ℝ)*τ/(2*(n:ℝ)^8) ≤ (I.card:ℝ) := by
  filter_upwards [GreedyGrowingFailure.eventually_independent (A+27),
    eventually_real_le_nat 2] with n hm hm2
  intro τ hτ hbudget α _ _ hVA H hlin hfour hdeg
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
  have hm12 : (5:ℝ) ≤ (n:ℝ)^24 := by
    have hp := pow_le_pow_right₀ hmone (show 3 ≤ 24 by omega)
    have h8 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hm2 3
    norm_num at h8
    linarith only [hp,h8]
  have hm12n : 5 ≤ n^24 := by exact_mod_cast hm12
  obtain ⟨p,hprime,hpD,hp3,hpup,G,hGfour,hGreg,_hGpair,hGinter,htransfer⟩ :=
    exists_regularization_prime H (n^24) 1 hfour hdeg (by omega)
      (fun a b hab => hlin.pair_degree a b hab)
  letI : Fact p.Prime := ⟨hprime⟩
  have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
  have hplo : (n:ℝ)^24 ≤ p := by exact_mod_cast hpD
  have hpupper : (p:ℝ) ≤ 2*(n:ℝ)^24 := by
    have hh := hpup
    rw [max_eq_left hm12n] at hh
    exact_mod_cast hh
  have hGV : (Fintype.card (Vertex α (ZMod p)):ℝ) = 4*(p:ℝ)*(Fintype.card α:ℝ) := by
    simp only [vertex_card,ZMod.card,Nat.cast_mul,Nat.cast_ofNat]
  have hGlo : (n:ℝ)^24 ≤ (Fintype.card (Vertex α (ZMod p)):ℝ) := by
    rw [hGV]
    have hpv := mul_le_mul_of_nonneg_left hcardone hp0.le
    nlinarith only [hplo,hpv,hp0.le]
  have hGhi0 : (Fintype.card (Vertex α (ZMod p)):ℝ) ≤ (n:ℝ)^(A+27) := by
    rw [hGV]
    have h1 := mul_le_mul hpupper hVA hcardpos.le (by positivity : (0:ℝ) ≤ 2*(n:ℝ)^24)
    have h8 : (8:ℝ) ≤ (n:ℝ)^3 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hm2 3
      norm_num at hh
      exact hh
    have h2 := mul_le_mul_of_nonneg_right h8 (pow_nonneg hmpos.le (A+24))
    have he : (n:ℝ)^(A+27) = (n:ℝ)^A*(n:ℝ)^24*(n:ℝ)^3 := by
      rw [show A+27 = (A+24)+3 by omega,pow_add,pow_add]
    rw [he]
    rw [pow_add] at h2
    nlinarith only [h1,h2]
  have hGhi : (Fintype.card (Vertex α (ZMod p)):ℝ) ≤ (n:ℝ)^(2*(A+27)) :=
    hGhi0.trans (pow_le_pow_right₀ hmone (by omega))
  have hGlin : Linear G := hGinter 1 (by omega) hlin
  obtain ⟨B,hB,hBcard⟩ := hm τ hτ hbudget (Vertex α (ZMod p)) hGlo hGhi G hGlin hGfour hGreg
  obtain ⟨I,hI,hIcard⟩ := htransfer B hB
  refine ⟨I,hI,?_⟩
  have hIcard' : (B.card:ℝ) ≤ 4*(p:ℝ)*(I.card:ℝ) := by exact_mod_cast hIcard
  rw [hGV] at hBcard
  have hh : (4*(p:ℝ))*((Fintype.card α:ℝ)*τ/(2*(n:ℝ)^8)) ≤
      (4*(p:ℝ))*(I.card:ℝ) := by
    calc
      _ = (4*(p:ℝ)*(Fintype.card α:ℝ))*τ/(2*(n:ℝ)^8) := by ring
      _ ≤ (B.card:ℝ) := hBcard
      _ ≤ _ := hIcard'
  exact le_of_mul_le_mul_left hh (by positivity : (0:ℝ) < 4*(p:ℝ))

/-- Arbitrary finite carriers, with the same growing horizon and no loss
    during subtype transport. -/
theorem eventually_selection {α : Type*} [DecidableEq α] (Aexp : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ τ : ℝ, 1 ≤ τ → horizonBudget τ ≤ (n:ℝ) →
      ∀ A : Finset α, (A.card:ℝ) ≤ (n:ℝ)^Aexp →
      ∀ H : Finset (Finset α), (∀ e ∈ H, e ⊆ A) → (∀ e ∈ H, e.card = 4) →
      (∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 1) →
      (∀ a ∈ A, HypergraphDegreeTrim.degree H a ≤ n^24) →
      ∃ I ⊆ A, (∀ e ∈ H, ¬e ⊆ I) ∧ (A.card:ℝ)*τ/(2*(n:ℝ)^8) ≤ (I.card:ℝ) := by
  filter_upwards [eventually_independent Aexp] with n hn
  intro τ hτ hbudget A hcard H hH hfour hlin hdeg
  have hcard' : (Fintype.card A:ℝ) ≤ (n:ℝ)^Aexp := by simpa only [Fintype.card_coe] using hcard
  have hfour' : ∀ e ∈ GreedyAmbientExtraction.hypergraph A H, e.card = 4 := by
    intro e he
    obtain ⟨e,heH,rfl⟩ := mem_image.mp he
    rw [GreedyAmbientExtraction.lift_card (hH e heH),hfour e heH]
  have hdeg' : ∀ a : A, HypergraphDegreeTrim.degree (GreedyAmbientExtraction.hypergraph A H) a ≤ n^24 := by
    intro a
    rw [GreedyAmbientExtraction.degree_lift hH]
    exact hdeg a.val a.property
  obtain ⟨I,hI,hIc⟩ := hn τ hτ hbudget A hcard' (GreedyAmbientExtraction.hypergraph A H)
    (GreedyAmbientExtraction.linear_lift hH hlin) hfour' hdeg'
  refine ⟨I.map (Function.Embedding.subtype _),?_,GreedyAmbientExtraction.project_independent hH hI,?_⟩
  · intro a ha
    obtain ⟨a,ha,rfl⟩ := mem_map.mp ha
    exact a.property
  · simpa only [card_map,Fintype.card_coe] using hIc

#print axioms eventually_independent
#print axioms eventually_selection
end
end Erdos773.GreedyGrowingExtraction
