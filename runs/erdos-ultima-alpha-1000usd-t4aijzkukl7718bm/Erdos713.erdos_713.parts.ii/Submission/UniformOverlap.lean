import FormalConjecturesUtil
import Submission.UniformIncidence

/-! Uniformly few pairs have common-neighbor count of the extremal degree
scale. This uses no extremality or maximum-degree assumption on the host. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Topology
namespace Erdos713UniformOverlap
open Erdos713UniformIncidence
variable {V W : Type*}
set_option maxHeartbeats 2000000

lemma sum_degree_sq_split [Fintype V] (G : SimpleGraph V) (S : Finset V) {L : ℝ}
    (hL : 0 ≤ L) (hLow : ∀ v, v ∉ S → (Nat.card (G.neighborSet v) : ℝ) ≤ L) :
    (∑ v : V, (Nat.card (G.neighborSet v) : ℝ)^2) ≤
      (Fintype.card V : ℝ)*(∑ v ∈ S, (Nat.card (G.neighborSet v) : ℝ)) +
      L*(∑ v : V, (Nat.card (G.neighborSet v) : ℝ)) := by
  classical
  have hv (v : V) : (Nat.card (G.neighborSet v) : ℝ)^2 ≤
      (if v ∈ S then (Fintype.card V : ℝ)*(Nat.card (G.neighborSet v) : ℝ) else 0)+
      L*(Nat.card (G.neighborSet v) : ℝ) := by
    have hd : (0 : ℝ) ≤ Nat.card (G.neighborSet v) := Nat.cast_nonneg _
    by_cases hs : v ∈ S
    · rw [if_pos hs]
      have hn : (Nat.card (G.neighborSet v) : ℝ) ≤ Fintype.card V := by
        have hcard : Nat.card (G.neighborSet v) ≤ Fintype.card V := by
          simpa only [Nat.card_eq_fintype_card] using
            Nat.card_le_card_of_injective (fun x : G.neighborSet v => x.val) Subtype.val_injective
        exact_mod_cast hcard
      nlinarith [mul_nonneg hL hd]
    · rw [if_neg hs,zero_add]
      nlinarith [hLow v hs]
  have hh := sum_le_sum (s := (univ : Finset V)) (fun v _ => hv v)
  simpa only [sum_add_distrib,← sum_filter,filter_mem_eq_inter,univ_inter,← mul_sum] using hh

lemma power_ratio_eventually {α K η : ℝ} (ha2 : α < 2) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, K*(n : ℝ)^(α-1) ≤ η*n := by
  have hz : Tendsto (fun n : ℕ => K*(n : ℝ)^(α-2)) atTop (𝓝 0) := by
    simpa only [neg_sub,mul_zero] using
      (((tendsto_rpow_neg_atTop (show 0 < 2-α by linarith)).comp
        tendsto_natCast_atTop_atTop).const_mul K)
  filter_upwards [hz.eventually_lt_const hη,eventually_gt_atTop (0 : ℕ)] with n hn hnp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnp
  have he : (n : ℝ)^(α-1) = (n : ℝ)^(α-2)*(n : ℝ) := by
    calc
      _ = (n : ℝ)^((α-2)+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hnR,Real.rpow_one]
  rw [he,← mul_assoc]
  exact mul_le_mul_of_nonneg_right hn.le hnR.le

/-- The second degree moment is o(n^(alpha+1)), uniformly over H-free
hosts of order n, provided 1<alpha<2 and the stated extremal asymptotic. -/
theorem small_second_moment (H : SimpleGraph W) {α c ε : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → H.Free G →
      (∑ v : V, (Nat.card (G.neighborSet v) : ℝ)^2) ≤ ε*(n : ℝ)^(α+1) := by
  classical
  obtain ⟨K,hK,hMass⟩ := high_degree_mass H ha hc h (by positivity : 0 < ε/2)
  have hUpper : ∀ᶠ n : ℕ in atTop, (extremalNumber n H : ℝ) ≤ 2*c*(n : ℝ)^α := by
    filter_upwards [(Erdos713FutureRecords.ratio_limit h).eventually_lt_const
      (show c < 2*c by linarith),eventually_gt_atTop (0 : ℕ)] with n hn hnp
    exact ((div_lt_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hnp) α)).mp hn).le
  filter_upwards [hMass,hUpper,power_ratio_eventually (K := K) ha2
    (show 0 < ε/(8*c) by positivity),eventually_gt_atTop (0 : ℕ)] with n hM hU hRatio hn
  intro V instV G hcard hf
  let S := (univ : Finset V).filter (fun v => K*(n : ℝ)^(α-1) ≤ (Nat.card (G.neighborSet v) : ℝ))
  have hS : (∑ v ∈ S, (Nat.card (G.neighborSet v) : ℝ)) ≤ (ε/2)*(n : ℝ)^α :=
    hM V G hcard hf S (fun v hv => (mem_filter.mp hv).2)
  have hLow (v : V) (hv : v ∉ S) : (Nat.card (G.neighborSet v) : ℝ) ≤ K*(n : ℝ)^(α-1) := by
    have hh : ¬ K*(n : ℝ)^(α-1) ≤ (Nat.card (G.neighborSet v) : ℝ) := by simpa [S] using hv
    exact (lt_of_not_ge hh).le
  have hSplit := sum_degree_sq_split G S (show 0 ≤ K*(n : ℝ)^(α-1) by positivity) hLow
  have hsum : (∑ v : V, (Nat.card (G.neighborSet v) : ℝ)) = 2*(Nat.card G.edgeSet : ℝ) := by
    exact_mod_cast (by
      simpa only [← card_neighborSet_eq_degree,edgeFinset_card,Fintype.card_eq_nat_card] using
        G.sum_degrees_eq_twice_card_edges)
  have hedge : (Nat.card G.edgeSet : ℝ) ≤ 2*c*(n : ℝ)^α := by
    have hh : Nat.card G.edgeSet ≤ extremalNumber n H := by
      simpa only [hcard,edgeFinset_card,Nat.card_eq_fintype_card] using card_edgeFinset_le_extremalNumber hf
    exact (show (Nat.card G.edgeSet : ℝ) ≤ (extremalNumber n H : ℝ) by exact_mod_cast hh).trans hU
  rw [hsum,hcard] at hSplit
  have hh := mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hl := mul_le_mul hRatio (show 2*(Nat.card G.edgeSet : ℝ) ≤ 4*c*(n : ℝ)^α by linarith)
    (by positivity) (by positivity)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (n : ℝ)^(α+1) = (n : ℝ)^α*n := by rw [Real.rpow_add hnR,Real.rpow_one]
  have hc0 : c ≠ 0 := hc.ne'
  have he : (ε/(8*c)*n)*(4*c*(n : ℝ)^α) = (ε/2)*(n : ℝ)^α*n := by field_simp; ring
  rw [he] at hl
  rw [hpow]
  nlinarith only [hSplit,hh,hl]

open scoped Classical in
noncomputable def highOverlap [Fintype V] (G : SimpleGraph V) (t : ℝ) : Finset (V × V) :=
  univ.filter (fun p => t < (Nat.card (G.commonNeighbors p.1 p.2) : ℝ))

lemma highOverlap_count [Fintype V] (G : SimpleGraph V) (t : ℝ) :
    t*(highOverlap G t).card ≤ ∑ v : V, (Nat.card (G.neighborSet v) : ℝ)^2 := by
  classical
  have hh := sum_le_sum (s := highOverlap G t) (fun p hp => (mem_filter.mp hp).2.le)
  simp only [sum_const,nsmul_eq_mul] at hh
  have hsub := sum_le_sum_of_subset_of_nonneg
    (f := fun p : V × V => (Nat.card (G.commonNeighbors p.1 p.2) : ℝ))
    (subset_univ (highOverlap G t))
    (fun p _ _ => Nat.cast_nonneg (Nat.card (G.commonNeighbors p.1 p.2)))
  have he : (∑ p : V × V, (Nat.card (G.commonNeighbors p.1 p.2) : ℝ)) =
      ∑ v : V, (Nat.card (G.neighborSet v) : ℝ)^2 := by
    exact_mod_cast (by
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using
        Erdos713DRC.sum_common_eq_sum_degree_sq G)
  nlinarith only [hh,hsub,he]

/-- Only o(n^2) ordered pairs have overlap exceeding a*n^(alpha-1). -/
theorem few_high_overlaps (H : SimpleGraph W) {α c a ε : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c) (ha0 : 0 < a)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → H.Free G →
      (highOverlap G (a*(n : ℝ)^(α-1))).card ≤ ε*(n : ℝ)^2 := by
  filter_upwards [small_second_moment H ha ha2 hc h (mul_pos hε ha0),
    eventually_gt_atTop (0 : ℕ)] with n hM hn
  intro V instV G hcard hf
  have hb := (highOverlap_count G (a*(n : ℝ)^(α-1))).trans (hM V G hcard hf)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (ε*a)*(n : ℝ)^(α+1) = (a*(n : ℝ)^(α-1))*(ε*(n : ℝ)^2) := by
    have hp : (n : ℝ)^(α+1) = (n : ℝ)^(α-1)*(n : ℝ)^2 := by
      calc
        _ = (n : ℝ)^((α-1)+2) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add hnR,Real.rpow_two]
    rw [hp]
    ring
  rw [he] at hb
  exact (mul_le_mul_iff_right₀ (mul_pos ha0 (Real.rpow_pos_of_pos hnR _))).mp hb

#print axioms small_second_moment
#print axioms few_high_overlaps
end Erdos713UniformOverlap
