import Submission.GreedyPolynomialExtraction

/-!
Removal of exact regularity by the verified polynomial-size regularization.
The independent-set density transfers with no further loss.
-/
namespace Erdos773.GreedyBoundedDegreeExtraction
open Finset Filter GreedyLinearDrift GreedyHypergraphState FourUniformRegularization
open GreedyPolynomialExtraction
set_option maxHeartbeats 2500000
noncomputable section

/-- For every fixed polynomial volume bound and every fixed normalized
    horizon, bounded-degree linear four-uniform hypergraphs eventually have
    the same independent-set lower bound as their regularizations. -/
theorem eventually_independent (A : ℕ) (τ : ℝ) (hτ : 1 ≤ τ) :
    ∀ᶠ m : ℕ in atTop, ∀ (α : Type*) [Fintype α] [DecidableEq α],
      (Fintype.card α:ℝ) ≤ (m:ℝ)^A →
      ∀ H : Finset (Finset α), Linear H → (∀ e ∈ H, e.card = 4) →
      (∀ u : α, HypergraphDegreeTrim.degree H u ≤ m^12) →
      ∃ I : Finset α, Independent H I ∧
        (Fintype.card α:ℝ)*τ/(2*(m:ℝ)^4) ≤ (I.card:ℝ) := by
  filter_upwards [GreedyPolynomialExtraction.eventually_independent (A+15) τ hτ,
    eventually_real_le_nat 2] with m hm hm2
  intro α _ _ hVA H hlin hfour hdeg
  by_cases hzero : Fintype.card α = 0
  · refine ⟨∅,?_,?_⟩
    · intro e he hsub
      have hh := card_le_card hsub
      rw [hfour e he,card_empty] at hh
      omega
    · simp only [hzero,Nat.cast_zero,zero_mul,zero_div,card_empty,le_refl]
  have hcardpos : (0:ℝ) < Fintype.card α := by exact_mod_cast Nat.pos_of_ne_zero hzero
  have hcardone : (1:ℝ) ≤ Fintype.card α := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
  have hmpos : (0:ℝ) < m := by linarith
  have hmone : (1:ℝ) ≤ m := by linarith
  have hm12 : (5:ℝ) ≤ (m:ℝ)^12 := by
    have hp := pow_le_pow_right₀ hmone (show 3 ≤ 12 by omega)
    have h8 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hm2 3
    norm_num at h8
    linarith only [hp,h8]
  have hm12n : 5 ≤ m^12 := by exact_mod_cast hm12
  obtain ⟨p,hprime,hpD,hp3,hpup,G,hGfour,hGreg,_hGpair,hGinter,htransfer⟩ :=
    exists_regularization_prime H (m^12) 1 hfour hdeg (by omega)
      (fun a b hab => hlin.pair_degree a b hab)
  letI : Fact p.Prime := ⟨hprime⟩
  have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
  have hplo : (m:ℝ)^12 ≤ p := by exact_mod_cast hpD
  have hpupper : (p:ℝ) ≤ 2*(m:ℝ)^12 := by
    have hh := hpup
    rw [max_eq_left hm12n] at hh
    exact_mod_cast hh
  have hGV : (Fintype.card (Vertex α (ZMod p)):ℝ) = 4*(p:ℝ)*(Fintype.card α:ℝ) := by
    simp only [vertex_card,ZMod.card,Nat.cast_mul,Nat.cast_ofNat]
  have hGlo : (m:ℝ)^12 ≤ (Fintype.card (Vertex α (ZMod p)):ℝ) := by
    rw [hGV]
    have hpv := mul_le_mul_of_nonneg_left hcardone hp0.le
    nlinarith only [hplo,hpv,hp0.le]
  have hGhi : (Fintype.card (Vertex α (ZMod p)):ℝ) ≤ (m:ℝ)^(A+15) := by
    rw [hGV]
    have h1 := mul_le_mul hpupper hVA hcardpos.le (by positivity : (0:ℝ) ≤ 2*(m:ℝ)^12)
    have h8 : (8:ℝ) ≤ (m:ℝ)^3 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hm2 3
      norm_num at hh
      exact hh
    have h2 := mul_le_mul_of_nonneg_right h8 (pow_nonneg hmpos.le (A+12))
    have he : (m:ℝ)^(A+15) = (m:ℝ)^A*(m:ℝ)^12*(m:ℝ)^3 := by
      rw [show A+15 = (A+12)+3 by omega,pow_add,pow_add]
    rw [he]
    rw [pow_add] at h2
    nlinarith only [h1,h2]
  have hGlin : Linear G := hGinter 1 (by omega) hlin
  obtain ⟨B,hB,hBcard⟩ := hm (Vertex α (ZMod p)) hGlo hGhi G hGlin hGfour hGreg
  obtain ⟨I,hI,hIcard⟩ := htransfer B hB
  refine ⟨I,hI,?_⟩
  have hIcard' : (B.card:ℝ) ≤ 4*(p:ℝ)*(I.card:ℝ) := by exact_mod_cast hIcard
  rw [hGV] at hBcard
  have hh : (4*(p:ℝ))*((Fintype.card α:ℝ)*τ/(2*(m:ℝ)^4)) ≤
      (4*(p:ℝ))*(I.card:ℝ) := by
    calc
      _ = (4*(p:ℝ)*(Fintype.card α:ℝ))*τ/(2*(m:ℝ)^4) := by ring
      _ ≤ (B.card:ℝ) := hBcard
      _ ≤ _ := hIcard'
  exact le_of_mul_le_mul_left hh (by positivity : (0:ℝ) < 4*(p:ℝ))

/-- In particular the multiplier over the elementary V/D^(1/3) scale is
    unbounded, for polynomially bounded volumes and D=m^12. -/
theorem eventually_arbitrary_multiplier (A : ℕ) (c : ℝ) :
    ∀ᶠ m : ℕ in atTop, ∀ (α : Type*) [Fintype α] [DecidableEq α],
      (Fintype.card α:ℝ) ≤ (m:ℝ)^A →
      ∀ H : Finset (Finset α), Linear H → (∀ e ∈ H, e.card = 4) →
      (∀ u : α, HypergraphDegreeTrim.degree H u ≤ m^12) →
      ∃ I : Finset α, Independent H I ∧
        c*(Fintype.card α:ℝ)/(m:ℝ)^4 ≤ (I.card:ℝ) := by
  filter_upwards [eventually_independent A (max 1 (2*c)) (le_max_left _ _)] with m hm
  intro α _ _ hV H hlin hfour hdeg
  obtain ⟨I,hI,hcard⟩ := hm α hV H hlin hfour hdeg
  refine ⟨I,hI,le_trans ?_ hcard⟩
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right 1 (2*c)) (Nat.cast_nonneg (Fintype.card α)))
    (by positivity : (0:ℝ) ≤ 2*(m:ℝ)^4)
  convert hh using 1 <;> ring

#print axioms eventually_independent
#print axioms eventually_arbitrary_multiplier
end
end Erdos773.GreedyBoundedDegreeExtraction
