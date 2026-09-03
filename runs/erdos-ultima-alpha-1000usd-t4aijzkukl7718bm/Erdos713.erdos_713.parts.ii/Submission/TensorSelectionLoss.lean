import FormalConjecturesUtil
import Submission.TensorEdgeSelection
import Submission.NearFullPenaltyWitnesses

/-! Uniform loss of the extremal scale in H-free spanning edge selections
from tensor squares of bounded-degree factors. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology
namespace Erdos713TensorSelectionLoss
open Erdos713ProductCover Erdos713DegreePenalty Erdos713NearFullPenaltyWitnesses
variable {V U W : Type*}
set_option maxHeartbeats 1000000

lemma bounded_degrees [Fintype V] [Fintype U] (H : SimpleGraph W) (G : SimpleGraph V)
    (F : SimpleGraph U) (J : SimpleGraph (V × U)) (hJ : J ≤ tensor G F) (hf : H.Free J)
    {α C B DG DF : ℝ} (ha : 0 ≤ α) (hC : 0 ≤ C)
    (hUpper : ∀ s : ℕ, (extremalNumber s H : ℝ) ≤ C*(s : ℝ)^α+B)
    (hG : ∀ v, degreeR G v ≤ DG) (hF : ∀ u, degreeR F u ≤ DF) :
    2*edgesR J ≤ (Fintype.card V : ℝ)*Fintype.card U*(C*(DG+DF)^α+B) := by
  have hh := Erdos713TensorEdgeSelection.edge_bound H G F J hJ hf
  have hR : 2*edgesR J ≤ ∑ v : V, ∑ u : U,
      (extremalNumber (Nat.card (F.neighborSet u)+Nat.card (G.neighborSet v)) H : ℝ) := by
    unfold edgesR
    exact_mod_cast hh
  apply hR.trans
  calc
    _ ≤ ∑ _v : V, ∑ _u : U, (C*(DG+DF)^α+B) := by
      apply sum_le_sum
      intro v _
      apply sum_le_sum
      intro u _
      apply (hUpper _).trans
      have hd : ((Nat.card (F.neighborSet u)+Nat.card (G.neighborSet v) : ℕ) : ℝ) ≤ DG+DF := by
        rw [Nat.cast_add]
        change degreeR F u+degreeR G v ≤ _
        linarith [hG v,hF u]
      exact add_le_add (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hd ha) hC) le_rfl
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]; ring

lemma self_bound {n : ℕ} (H : SimpleGraph W) (G : SimpleGraph (Fin n))
    (J : SimpleGraph (Fin n × Fin n)) (hJ : J ≤ tensor G G) (hf : H.Free J)
    {α C B D : ℝ} (ha : 0 ≤ α) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hUpper : ∀ s : ℕ, (extremalNumber s H : ℝ) ≤ C*(s : ℝ)^α+B)
    (hG : ∀ v, degreeR G v ≤ D*(n : ℝ)^(α-1)) :
    2*edgesR J ≤ (n : ℝ)^2*(C*(2*D)^α*(n : ℝ)^((α-1)*α)+B) := by
  have hh := bounded_degrees H G G J hJ hf ha hC hUpper hG hG
  simp only [Fintype.card_fin] at hh
  have he : (D*(n : ℝ)^(α-1)+D*(n : ℝ)^(α-1))^α =
      (2*D)^α*(n : ℝ)^((α-1)*α) := by
    rw [show D*(n : ℝ)^(α-1)+D*(n : ℝ)^(α-1)=(2*D)*(n : ℝ)^(α-1) by ring,
      Real.mul_rpow (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      ← Real.rpow_mul (Nat.cast_nonneg _)]
  rw [he] at hh
  nlinarith only [hh]

/-- At all sufficiently large orders, EVERY H-free spanning edge selection
from EVERY factor satisfying the degree cap has at most eps times the
ordinary extremal number on the full product vertex set. -/
theorem eventual_loss (H : SimpleGraph W) {α c D : ℝ} (ha : 1 < α) (ha2 : α < 2)
    (hc : 0 < c) (hD : 0 < D)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (∀ v, degreeR G v ≤ D*(n : ℝ)^(α-1)) →
      ∀ J : SimpleGraph (Fin n × Fin n), J ≤ tensor G G → H.Free J →
        edgesR J ≤ ε*(extremalNumber (n*n) H : ℝ) := by
  obtain ⟨B,_,hUpper⟩ := global_upper_envelope H hc (show (0 : ℝ) < 1 by norm_num) h
  let A := (c+1)*(2*D)^α
  let g := (α-1)*(α-2)
  have hg : g < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have hk : 2-2*α < 0 := by linarith
  let L : ℕ → ℝ := fun n => A*(n : ℝ)^g+B*(n : ℝ)^(2-2*α)
  have hg0 : Tendsto (fun n : ℕ => (n : ℝ)^g) atTop (𝓝 0) := by
    simpa only [neg_neg] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hg)).comp tendsto_natCast_atTop_atTop
  have hk0 : Tendsto (fun n : ℕ => (n : ℝ)^(2-2*α)) atTop (𝓝 0) := by
    simpa only [neg_neg] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hk)).comp tendsto_natCast_atTop_atTop
  have hL : Tendsto L atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using (hg0.const_mul A).add (hk0.const_mul B)
  have hSquare : Tendsto (fun n : ℕ => n*n) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b,eventually_ge_atTop (1 : ℕ)] with n hb hn
    nlinarith
  have hRatio := (Erdos713FutureRecords.ratio_limit h).comp hSquare
  filter_upwards [hL.eventually_lt_const (mul_pos hε hc),
    hRatio.eventually_const_lt (show c/2 < c by linarith),eventually_gt_atTop (0 : ℕ)]
    with n hSmall hLow hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hPow : 0 < (n : ℝ)^(2*α) := Real.rpow_pos_of_pos hnR _
  have hSquarePow : ((n*n : ℕ) : ℝ)^α=(n : ℝ)^(2*α) := by
    rw [Nat.cast_mul,Real.mul_rpow hnR.le hnR.le,← Real.rpow_add hnR]
    congr 1
    ring
  change c/2 < (extremalNumber (n*n) H : ℝ)/((n*n : ℕ) : ℝ)^α at hLow
  rw [hSquarePow] at hLow
  have hLow' := ((lt_div_iff₀ hPow).mp hLow).le
  have hIdentity : L n*(n : ℝ)^(2*α) =
      (n : ℝ)^2*((c+1)*(2*D)^α*(n : ℝ)^((α-1)*α)+B) := by
    dsimp only [L]
    calc
      _ = A*(n : ℝ)^(g+2*α)+B*(n : ℝ)^((2-2*α)+2*α) := by
        rw [Real.rpow_add hnR,Real.rpow_add hnR]
        ring
      _ = A*((n : ℝ)^2*(n : ℝ)^((α-1)*α))+B*(n : ℝ)^2 := by
        rw [show g+2*α=2+(α-1)*α by dsimp [g]; ring,
          show (2-2*α)+2*α=(2 : ℝ) by ring,Real.rpow_add hnR,Real.rpow_two]
      _ = _ := by dsimp [A]; ring
  intro G hG J hJ hf
  have hBound := self_bound H G J hJ hf (by linarith : 0 ≤ α)
    (by positivity : 0 ≤ c+1) hD.le hUpper hG
  rw [← hIdentity] at hBound
  have hSmall' := mul_le_mul_of_nonneg_right hSmall.le hPow.le
  have hLow'' := mul_le_mul_of_nonneg_left hLow' (show 0 ≤ 2*ε by positivity)
  nlinarith only [hBound,hSmall',hLow'']

#print axioms bounded_degrees
#print axioms self_bound
#print axioms eventual_loss
end Erdos713TensorSelectionLoss
