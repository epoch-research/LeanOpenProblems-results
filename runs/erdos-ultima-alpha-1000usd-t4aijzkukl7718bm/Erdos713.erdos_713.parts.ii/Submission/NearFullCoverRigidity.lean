import FormalConjecturesUtil
import Submission.CoverSheetCounts

/-! Near-full graphs cannot be nontrivial ordinary covers of connected
H-free bases under a superlinear pure-power extremal asymptotic.
The base-freeness condition is essential and explicitly retained.
This necessary condition does not prove rationality. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Classical
namespace Erdos713NearFullCoverRigidity
open Erdos713ProductCover Erdos713CoverSheetCounts
set_option maxHeartbeats 2000000

lemma upper_envelope (f : ℕ → ℕ) {α c η : ℝ} (hc : 0 < c) (hη : 0 < η)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, (f n : ℝ) ≤ (c+η)*(n : ℝ)^α+B := by
  have he : ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (c+η)*(n : ℝ)^α := by
    filter_upwards [h.isLittleO.def (show 0 < η/c by positivity)] with n hn
    have hp : 0 ≤ (n : ℝ)^α := Real.rpow_nonneg (Nat.cast_nonneg n) _
    simp only [Pi.sub_apply,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hc.le hp)] at hn
    have hh := (le_abs_self ((f n : ℝ)-c*(n : ℝ)^α)).trans hn
    have hcoef : (η/c)*c=η := div_mul_cancel₀ η hc.ne'
    rw [← mul_assoc,hcoef] at hh
    nlinarith only [hh]
  obtain ⟨L,hL⟩ := eventually_atTop.mp he
  let B : ℕ := ∑ j ∈ range L, f j
  refine ⟨B,Nat.cast_nonneg _,?_⟩
  intro n
  by_cases hn : L ≤ n
  · exact (hL n hn).trans (le_add_of_nonneg_right (Nat.cast_nonneg B))
  · have hnB : f n ≤ B := single_le_sum (s := range L) (f := f)
      (fun _ _ => Nat.zero_le _) (mem_range.mpr (by omega))
    have hcast : (f n : ℝ) ≤ B := by exact_mod_cast hnB
    have hp : 0 ≤ (c+η)*(n : ℝ)^α := by positivity
    linarith

lemma linear_negligible {α ε B : ℝ} (ha : 1 < α) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, B*(n : ℝ) < ε*(n : ℝ)^α := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^(α-1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < α-1)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_gt_atTop (B/ε),eventually_gt_atTop (0 : ℕ)] with n hn hnp
  have hp : (0 : ℝ) < n := by exact_mod_cast hnp
  have hh : B < ε*(n : ℝ)^(α-1) := by
    have h' := (div_lt_iff₀ hε).mp hn
    simpa only [mul_comm] using h'
  have heq : (n : ℝ)^α = (n : ℝ)^(α-1)*(n : ℝ) := by
    calc
      _ = (n : ℝ)^(α-1+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hp,Real.rpow_one]
  rw [heq]
  nlinarith only [mul_lt_mul_of_pos_right hh hp]

/-- Uniform over all factorizations n=t*m, including those for which m
stays small. A linear error from the all-order envelope handles that case. -/
theorem sheet_density_gap (f : ℕ → ℕ) {α c : ℝ} (ha : 1 < α) (hc : 0 < c)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop, ∀ m t : ℕ,
      2 ≤ t → n=t*m → (t : ℝ)*(f m : ℝ) < (c-ε)*(n : ℝ)^α := by
  let s : ℝ := 2^(1-α)
  have hs0 : 0 < s := Real.rpow_pos_of_pos (by norm_num) _
  have hs1 : s < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let ε : ℝ := c*(1-s)/4
  have hε : 0 < ε := div_pos (mul_pos hc (sub_pos.mpr hs1)) (by norm_num)
  have hεs : ε*s ≤ ε := by nlinarith only [mul_le_mul_of_nonneg_left hs1.le hε.le]
  have heq : c*s+4*ε=c := by dsimp [ε]; ring
  have hco : (c+ε)*s+ε < c-ε := by nlinarith only [hεs,heq,hε]
  obtain ⟨B,hB,hEnvelope⟩ := upper_envelope f hc hε h
  refine ⟨ε,hε,?_⟩
  filter_upwards [linear_negligible ha hε (B := B),eventually_gt_atTop (0 : ℕ)] with n hErr hn
  intro m t ht hnt
  have hm : 0 < m := by
    by_contra hh
    have hz : m=0 := by omega
    rw [hz,Nat.mul_zero] at hnt
    omega
  have htn : t ≤ n := by nlinarith
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnEq : (n : ℝ)=(t : ℝ)*(m : ℝ) := by exact_mod_cast hnt
  have hpower : (t : ℝ)*(m : ℝ)^α ≤ s*(n : ℝ)^α := by
    have he : (t : ℝ)*(m : ℝ)^α / (n : ℝ)^α = (t : ℝ)^(1-α) := by
      rw [hnEq,normalized_formula hmR htR]
      rw [div_self (Real.rpow_pos_of_pos hmR α).ne',one_mul]
    have hb : (t : ℝ)^(1-α) ≤ s :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast ht) (by linarith)
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hnR α)).mp (he.trans_le hb)
  have hE := mul_le_mul_of_nonneg_left (hEnvelope m) htR.le
  have hMain := mul_le_mul_of_nonneg_left hpower (show 0 ≤ c+ε by positivity)
  have hRest := mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ n by exact_mod_cast htn) hB
  have hFinal := mul_lt_mul_of_pos_right hco (Real.rpow_pos_of_pos hnR α)
  nlinarith only [hE,hMain,hRest,hErr,hFinal]

/-- For one fixed positive density accuracy, every sufficiently large
near-full graph has no nontrivial cover map onto a connected H-free base.
The covering graph itself need not be assumed H-free in this statement. -/
theorem eventually_bijective {T : Type*} (H : SimpleGraph T) {α c : ℝ}
    (ha : 1 < α) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ (V W : Type) [Fintype V] [Fintype W],
      ∀ (G : SimpleGraph V) (F : SimpleGraph W) (f : G →g F),
      N ≤ Fintype.card V → IsCover f → F.Connected → H.Free F →
      (c-ε)*(Fintype.card V : ℝ)^α ≤ (Nat.card G.edgeSet : ℝ) →
      Function.Bijective f := by
  obtain ⟨ε,hε,hGap⟩ := sheet_density_gap (fun n => extremalNumber n H) ha hc h
  obtain ⟨N,hN⟩ := eventually_atTop.mp hGap
  refine ⟨ε,hε,N,?_⟩
  intro V W instV instW G F f hn hf hConn hFree hDense
  obtain ⟨t,ht,hFib,hVerts,hEdges⟩ := connected_counts f hf hConn
  have htOne : t=1 := by
    by_contra hh
    have htTwo : 2 ≤ t := by omega
    have hG := hN (Fintype.card V) hn (Fintype.card W) t htTwo hVerts
    have hBase : Nat.card F.edgeSet ≤ extremalNumber (Fintype.card W) H := by
      simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using card_edgeFinset_le_extremalNumber hFree
    have hE : Nat.card G.edgeSet ≤ t*extremalNumber (Fintype.card W) H := by
      rw [hEdges]
      exact Nat.mul_le_mul_left t hBase
    have hER : (Nat.card G.edgeSet : ℝ) ≤ (t : ℝ)*(extremalNumber (Fintype.card W) H : ℝ) := by
      exact_mod_cast hE
    linarith
  refine ⟨?_,hf.1⟩
  intro u v huv
  have hcard : Fintype.card {x // f x=f u} ≤ 1 := by
    have hh := hFib (f u)
    simpa only [Nat.card_eq_fintype_card,htOne] using hh.le
  letI : Subsingleton {x // f x=f u} := ⟨Fintype.card_le_one_iff.mp hcard⟩
  exact congrArg Subtype.val (Subsingleton.elim (⟨u,rfl⟩ : {x // f x=f u}) ⟨v,huv.symm⟩)

#print axioms upper_envelope
#print axioms sheet_density_gap
#print axioms eventually_bijective
end Erdos713NearFullCoverRigidity
