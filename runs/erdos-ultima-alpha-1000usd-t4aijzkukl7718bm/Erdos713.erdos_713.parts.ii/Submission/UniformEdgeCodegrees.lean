import FormalConjecturesUtil
import Submission.UniformEdgePenalty
import Submission.CycleNeighborhoodOverlap

/-! Edge-codegree tails in almost-regular H-free hosts with subquadratic
extremal growth. The order threshold may depend on the degree-cap constant. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical Topology
namespace Erdos713UniformEdgeCodegrees
open Erdos713DegreePenalty Erdos713CycleNeighborhoodOverlap
open Erdos713SmallSetIncidence Erdos713Cloning
variable {V W : Type*}
set_option maxHeartbeats 2000000

lemma neighborhood_free [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    (hf : H.Free G) (v : V) : H.Free (G.induce (G.neighborSet v)) :=
  fun h => hf (h.trans ⟨Copy.induce G _⟩)

lemma neighborhood_edges [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    (hf : H.Free G) {α C B D : ℝ} (ha : 1 < α) (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hU : ∀ m : ℕ, (extremalNumber m H : ℝ) ≤ C*(m : ℝ)^α+B*m)
    (hDeg : ∀ v, degreeR G v ≤ D) (v : V) :
    (Nat.card (G.induce (G.neighborSet v)).edgeSet : ℝ) ≤
      (C*D^(α-1)+B)*degreeR G v := by
  have he := card_edgeFinset_le_extremalNumber (neighborhood_free hf v)
  have heR : (Nat.card (G.induce (G.neighborSet v)).edgeSet : ℝ) ≤
      extremalNumber (Nat.card (G.neighborSet v)) H := by
    exact_mod_cast (by simpa only [edgeFinset_card,Nat.card_eq_fintype_card] using he)
  have hu := hU (Nat.card (G.neighborSet v))
  change (_ : ℝ) ≤ C*(degreeR G v)^α+B*degreeR G v at hu
  have hPow := Real.rpow_le_rpow (degreeR_nonneg G v) (hDeg v) (show 0 ≤ α-1 by linarith)
  have hh := mul_le_mul_of_nonneg_left hPow (mul_nonneg hC (degreeR_nonneg G v))
  have hfac := rpow_factor (degreeR_nonneg G v) ha
  rw [hfac] at hu
  nlinarith only [heR,hu,hh]

lemma codegree_sum_bound [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    (hf : H.Free G) {α C B D : ℝ} (ha : 1 < α) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hU : ∀ m : ℕ, (extremalNumber m H : ℝ) ≤ C*(m : ℝ)^α+B*m)
    (hDeg : ∀ v, degreeR G v ≤ D) :
    (∑ p : V × V, if G.Adj p.1 p.2 then (Nat.card (G.commonNeighbors p.1 p.2) : ℝ) else 0) ≤
      4*(C*D^(α-1)+B)*edgesR G := by
  have hid : (∑ p : V × V, if G.Adj p.1 p.2 then (Nat.card (G.commonNeighbors p.1 p.2) : ℝ) else 0) =
      2*∑ v : V, (Nat.card (G.induce (G.neighborSet v)).edgeSet : ℝ) := by
    exact_mod_cast sum_adjacent_codegrees G
  rw [hid]
  have hs := sum_le_sum (s := (univ : Finset V)) (fun v _ => neighborhood_edges hf ha hC hD hU hDeg v)
  rw [← mul_sum,degreeR_sum] at hs
  linarith

lemma badEdges_bound [Fintype V] {H : SimpleGraph W} {G : SimpleGraph V}
    (hf : H.Free G) {α C B D : ℝ} (ha : 1 < α) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hU : ∀ m : ℕ, (extremalNumber m H : ℝ) ≤ C*(m : ℝ)^α+B*m)
    (hDeg : ∀ v, degreeR G v ≤ D) (t : ℝ) :
    t*(badEdges G t).card ≤ 4*(C*D^(α-1)+B)*edgesR G := by
  let w : V × V → ℝ := fun p =>
    if G.Adj p.1 p.2 then (Nat.card (G.commonNeighbors p.1 p.2) : ℝ) else 0
  have hlow : ∀ p ∈ badEdges G t, t ≤ w p := by
    intro p hp
    obtain ⟨ha,ht⟩ := (mem_filter.mp hp).2
    simpa only [w,if_pos ha] using ht.le
  have hs := sum_le_sum hlow
  have hsub := sum_le_univ_sum_of_nonneg (s := badEdges G t) (f := w)
    (fun p => by dsimp [w]; split_ifs <;> positivity)
  simp only [sum_const,nsmul_eq_mul] at hs
  have hb := codegree_sum_bound hf ha hC hD hU hDeg
  change (∑ p, w p) ≤ _ at hb
  nlinarith only [hs,hsub,hb]

/-- The exceptional ordered edges are measured relative to e(G), not n².
D is fixed before the eventual order threshold. -/
theorem eventually_few_codegree_edges (H : SimpleGraph W) {α c t ε D : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c) (ht : 0 < t) (hε : 0 < ε) (hD : 0 < D)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] (G : SimpleGraph V), H.Free G →
      (∀ v, degreeR G v ≤ D*(n : ℝ)^(α-1)) →
        ((badEdges G (t*(n : ℝ)^(α-1))).card : ℝ) ≤ ε*edgesR G := by
  obtain ⟨B,hB,hU⟩ := Erdos713RelativeExpansion.linear_error_upper
    (fun n => extremalNumber n H) (Erdos713Cloning.extremal_zero H)
    (show 0 < 2*c by positivity) (show c < 2*c by linarith) h
  let β := α-1
  have hβ : 0 < β := by dsimp [β]; linarith
  have hβ1 : β < 1 := by dsimp [β]; linarith
  have hneg : β*β-β < 0 := by nlinarith
  have hterm1 : Tendsto (fun n : ℕ => (8*c*D^β)*(n : ℝ)^(β*β-β)) atTop (𝓝 0) := by
    simpa only [mul_zero,neg_neg,Function.comp_apply] using
      ((tendsto_rpow_neg_atTop (show 0 < -(β*β-β) by linarith)).comp
        tendsto_natCast_atTop_atTop).const_mul (8*c*D^β)
  have hterm2 : Tendsto (fun n : ℕ => (4*B)*(n : ℝ)^(-β)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ((tendsto_rpow_neg_atTop hβ).comp tendsto_natCast_atTop_atTop).const_mul (4*B)
  have hlim : Tendsto (fun n : ℕ =>
      (8*c*D^β)*(n : ℝ)^(β*β-β)+(4*B)*(n : ℝ)^(-β)) atTop (𝓝 0) := by
    simpa only [add_zero] using hterm1.add hterm2
  filter_upwards [hlim.eventually_le_const (mul_pos hε ht),eventually_gt_atTop (0 : ℕ)] with n hn hn0
  intro V instV G hf hDeg
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hP : 0 < (n : ℝ)^β := Real.rpow_pos_of_pos hnR _
  have hb := badEdges_bound hf ha (show 0 ≤ 2*c by positivity)
    (mul_pos hD hP).le hU hDeg (t*(n : ℝ)^β)
  have hnorm : 4*(2*c*(D*(n : ℝ)^β)^β+B) ≤ ε*(t*(n : ℝ)^β) := by
    have hh := mul_le_mul_of_nonneg_right hn hP.le
    have hpow : (n : ℝ)^(β*β-β)*(n : ℝ)^β=(n : ℝ)^(β*β) := by
      rw [← Real.rpow_add hnR]
      congr 1
      ring
    have hinv : (n : ℝ)^(-β)*(n : ℝ)^β=1 := by
      rw [← Real.rpow_add hnR]
      simp
    rw [add_mul] at hh
    simp only [mul_assoc] at hh
    rw [hpow,hinv,mul_one] at hh
    rw [Real.mul_rpow hD.le hP.le,← Real.rpow_mul hnR.le]
    nlinarith only [hh]
  have he := mul_le_mul_of_nonneg_right hnorm (show 0 ≤ edgesR G by exact Nat.cast_nonneg _)
  have hh := hb.trans he
  apply (mul_le_mul_iff_right₀ (mul_pos ht hP)).mp
  nlinarith only [hh]

#print axioms eventually_few_codegree_edges
end Erdos713UniformEdgeCodegrees
