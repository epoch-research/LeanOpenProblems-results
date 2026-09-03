import FormalConjecturesUtil
import Submission.TensorVertexSelection
import Submission.NearFullPenaltyWitnesses

/-! Loss of the ordinary extremal scale for sufficiently large vertex
selections from bounded-degree tensor squares. This does not quantize the
exponent or exclude smaller selected vertex sets. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology
namespace Erdos713TensorVertexSelectionAsymptotic
open Erdos713ProductCover Erdos713TensorVertexSelection
variable {W : Type*}
set_option maxHeartbeats 1000000

lemma extremal_zero (H : SimpleGraph W) : extremalNumber 0 H = 0 := by
  apply Nat.eq_zero_of_le_zero
  change extremalNumber (Fintype.card (Fin 0)) H ≤ 0
  rw [extremalNumber_le_iff]
  intro G _ _
  have hg : G = ⊥ := Subsingleton.elim _ _
  simp [hg]

lemma linear_upper_envelope (H : SimpleGraph W) {α c η : ℝ}
    (ha : 0 < α) (hc : 0 < c) (hη : 0 < η)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, (extremalNumber n H : ℝ) ≤ (c+η)*(n : ℝ)^α+B*n := by
  obtain ⟨B,hB,hUpper⟩ := Erdos713NearFullPenaltyWitnesses.global_upper_envelope H hc hη h
  refine ⟨B,hB,?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp [extremal_zero,Real.zero_rpow ha.ne']
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    have hh := mul_le_mul_of_nonneg_left hnR hB
    have hu := hUpper n
    linarith

lemma selected_order_tendsto {α : ℝ} (ha : 0 ≤ α)
    (S : (n : ℕ) → Finset (Fin n × Fin n))
    (hSize : Tendsto (fun n : ℕ => ((S n).card : ℝ)/(n : ℝ)^α) atTop atTop) :
    Tendsto (fun n => (S n).card) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [hSize.eventually_ge_atTop (b : ℝ),eventually_ge_atTop (1 : ℕ)] with n hb hn
  have hpow : 1 ≤ (n : ℝ)^α := Real.one_le_rpow (by exact_mod_cast hn) ha
  have hp : 0 < (n : ℝ)^α := lt_of_lt_of_le zero_lt_one hpow
  have hm := (le_div_iff₀ hp).mp hb
  have hbm : (b : ℝ) ≤ (S n).card :=
    (le_mul_of_one_le_right (Nat.cast_nonneg _) hpow).trans hm
  exact_mod_cast hbm

/-- Under a positive pure-power asymptotic for ex(n,H), arbitrary H-free
selections supported on m(n) product vertices lose the ordinary extremal
scale when m(n)/n^alpha tends to infinity. Freeness is required only on
the selected vertices; the forbidden graph may have isolated vertices. -/
theorem extremal_scale_loss (H : SimpleGraph W) {α c D : ℝ}
    (ha : 1 < α) (hc : 0 < c) (hD : 0 ≤ D)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (G : (n : ℕ) → SimpleGraph (Fin n))
    (J : (n : ℕ) → SimpleGraph (Fin n × Fin n))
    (S : (n : ℕ) → Finset (Fin n × Fin n))
    (hG : ∀ n v, ((G n).degree v : ℝ) ≤ D*(n : ℝ)^(α-1))
    (hJ : ∀ n, J n ≤ tensor (G n) (G n))
    (hs : ∀ n, (J n).support ⊆ S n) (hf : ∀ n, H.Free ((J n).induce (S n : Set _)))
    (hSize : Tendsto (fun n : ℕ => ((S n).card : ℝ)/(n : ℝ)^α) atTop atTop) :
    Tendsto (fun n => (Nat.card (J n).edgeSet : ℝ)/(extremalNumber (S n).card H : ℝ))
      atTop (𝓝 0) := by
  have ha0 : 0 ≤ α := by linarith
  obtain ⟨B,hB,hUpper⟩ := linear_upper_envelope H (by linarith : 0 < α) hc
    (by norm_num : (0 : ℝ) < 1) h
  have hSizeInv : Tendsto (fun n : ℕ => (n : ℝ)^α/(S n).card) atTop (𝓝 0) := by
    have hh := hSize.inv_tendsto_atTop
    change Tendsto (fun n : ℕ => (((S n).card : ℝ)/(n : ℝ)^α)⁻¹) atTop (𝓝 0) at hh
    simpa only [inv_div] using hh
  have hE := power_scale_loss H ha (by positivity : 0 ≤ c+1) hB hD hUpper
    G J S hG hJ hs hf hSizeInv
  have hOrder := selected_order_tendsto ha0 S hSize
  have hR := (Erdos713FutureRecords.ratio_limit h).comp hOrder
  have hQ := hE.div hR hc.ne'
  rw [zero_div] at hQ
  apply hQ.congr'
  filter_upwards [hOrder.eventually_gt_atTop (0 : ℕ)] with n hn
  have hp : ((S n).card : ℝ)^α ≠ 0 :=
    (Real.rpow_pos_of_pos (by exact_mod_cast hn) _).ne'
  exact div_div_div_cancel_right₀ hp _ _

/-- Direct formulation for arbitrary graphs on the selected vertex sets. -/
theorem extremal_scale_loss_on_subsets (H : SimpleGraph W) {α c D : ℝ}
    (ha : 1 < α) (hc : 0 < c) (hD : 0 ≤ D)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (G : (n : ℕ) → SimpleGraph (Fin n)) (S : (n : ℕ) → Finset (Fin n × Fin n))
    (R : (n : ℕ) → SimpleGraph (S n))
    (hG : ∀ n v, ((G n).degree v : ℝ) ≤ D*(n : ℝ)^(α-1))
    (hR : ∀ n, R n ≤ (tensor (G n) (G n)).induce (S n : Set _))
    (hf : ∀ n, H.Free (R n))
    (hSize : Tendsto (fun n : ℕ => ((S n).card : ℝ)/(n : ℝ)^α) atTop atTop) :
    Tendsto (fun n => (Nat.card (R n).edgeSet : ℝ)/(extremalNumber (S n).card H : ℝ))
      atTop (𝓝 0) := by
  have hf' (n : ℕ) : H.Free ((extend (S n) (R n)).induce (S n : Set _)) := by
    rw [extend_induce]
    exact hf n
  have hh := extremal_scale_loss H ha hc hD h G (fun n => extend (S n) (R n)) S
    hG (fun n => extend_le (S n) (R n) (hR n)) (fun n => extend_support (S n) (R n)) hf' hSize
  simpa only [extend_edge_card] using hh

#print axioms extremal_zero
#print axioms linear_upper_envelope
#print axioms selected_order_tendsto
#print axioms extremal_scale_loss
#print axioms extremal_scale_loss_on_subsets
end Erdos713TensorVertexSelectionAsymptotic
