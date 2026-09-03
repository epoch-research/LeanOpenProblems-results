import Submission.CofinalMangoldtUnit

/-!
# Capturing a cofinal linear lower bound on a fixed geometric grid

Only one fixed multiplier is selected from a finite pool. The multiplier
is fixed before the scale tends to infinity. There is no assertion that
all geometric scales have the lower bound.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma geometric_upper_rounding (b L N : ℕ) (hb : 1 < b) (hL : 1 ≤ L) (hN : L ≤ N) :
    let m := Nat.log b (N/L)
    ∃ j ∈ Icc L (L*b), N ≤ j*b^m ∧ L*(j*b^m) ≤ (L+1)*N := by
  let m := Nat.log b (N/L)
  let M := b^m
  have hM : 0 < M := pow_pos (by omega) _
  have hdiv : 1 ≤ N/L := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using hN)
  have hLM : L*M ≤ N := by
    have h := Nat.pow_log_le_self b (by omega : N/L ≠ 0)
    change M ≤ N/L at h
    have hh : M*L ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp h
    simpa only [mul_comm] using hh
  have hNB : N < (L*b)*M := by
    have h := Nat.lt_pow_succ_log_self hb (N/L)
    change N/L < b^(m+1) at h
    rw [_root_.pow_succ] at h
    have h' : N < (M*b)*L := (Nat.div_lt_iff_lt_mul (by omega)).mp h
    nlinarith only [h']
  let j := N/M+1
  have hjL : L ≤ j := by
    have h := (Nat.le_div_iff_mul_le hM).mpr hLM
    dsimp [j]
    omega
  have hjB : j ≤ L*b := by
    have h : N/M < L*b := (Nat.div_lt_iff_lt_mul hM).mpr hNB
    dsimp [j]
    omega
  have hNj : N ≤ j*M := by
    have h := Nat.lt_mul_div_succ N hM
    dsimp [j]
    nlinarith only [h]
  have hjN : j*M ≤ N+M := by
    have h := Nat.div_mul_le_self N M
    dsimp [j]
    nlinarith only [h]
  refine ⟨j,mem_Icc.mpr ⟨hjL,hjB⟩,hNj,?_⟩
  change L*(j*M) ≤ (L+1)*N
  have h := Nat.mul_le_mul_left L hjN
  nlinarith only [h,hLM]

lemma frequently_geometric_grid_of_frequently_linear (F : ℕ → ℝ) (hF : Monotone F)
    (b L : ℕ) (hb : 1 < b) (hL : 1 ≤ L) (c : ℝ) (hc : 0 ≤ c)
    (H : ∃ᶠ N : ℕ in atTop, (c*((L : ℝ)+1)/L)*N < F N) :
    ∃ j ∈ Icc L (L*b), ∃ᶠ m : ℕ in atTop, c*(j*b^m : ℕ) < F (j*b^m) := by
  apply (frequently_exists_finset (Icc L (L*b))).mp
  rw [frequently_atTop]
  intro K
  obtain ⟨N,hNK,hgood⟩ := H.forall_exists_of_atTop (L*b^K)
  have hNL : L ≤ N := (Nat.le_mul_of_pos_right L (Nat.one_le_pow _ _ (by omega))).trans hNK
  obtain ⟨j,hj,hNj,hbudget⟩ := geometric_upper_rounding b L N hb hL hNL
  let m := Nat.log b (N/L)
  have hmK : K ≤ m := by
    apply Nat.le_log_of_pow_le hb
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa only [mul_comm] using hNK)
  refine ⟨m,hmK,j,hj,?_⟩
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hbudgetR : (L : ℝ)*(j*b^m : ℕ) ≤ ((L : ℝ)+1)*N := by exact_mod_cast hbudget
  have hsize : (j*b^m : ℕ) ≤ (((L : ℝ)+1)/L)*N := by
    have hh : (j*b^m : ℕ) ≤ (((L : ℝ)+1)*N)/L :=
      (le_div_iff₀ hLR).mpr (by nlinarith only [hbudgetR])
    convert hh using 1; ring
  have hcsize := mul_le_mul_of_nonneg_left hsize hc
  have hg : (c*((L : ℝ)+1)/L)*N < F (j*b^m) := hgood.trans_le (hF hNj)
  exact hcsize.trans_lt (by convert hg using 1; ring)

/-- A dense finite set of multipliers recovers every slope below the unit limsup. -/
theorem exists_fixed_geometric_grid_unit_lower (F : ℕ → ℝ) (hF : Monotone F)
    (H : ∀ c : ℝ, c < 1 → ∃ᶠ N : ℕ in atTop, c*N < F N)
    (b : ℕ) (hb : 1 < b) (c : ℝ) (hc : c < 1) :
    ∃ j : ℕ, 1 ≤ j ∧ ∃ᶠ m : ℕ in atTop, c*(j*b^m : ℕ) < F (j*b^m) := by
  let c' := max 0 c
  have hc' : 0 ≤ c' := le_max_left _ _
  have hc'1 : c' < 1 := max_lt (by norm_num) hc
  obtain ⟨L,hL⟩ := exists_nat_gt (max 1 (c'/(1-c')))
  have hL1 : 1 ≤ L := by
    have hh : (1 : ℝ) < L := (le_max_left _ _).trans_lt hL
    exact_mod_cast hh.le
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL1
  have hslope : c'*((L : ℝ)+1)/L < 1 := by
    have hh : c'/(1-c') < L := (le_max_right _ _).trans_lt hL
    have hm := (div_lt_iff₀ (sub_pos.mpr hc'1)).mp hh
    apply (div_lt_one hLR).mpr
    nlinarith only [hm]
  obtain ⟨j,hj,Hj⟩ := frequently_geometric_grid_of_frequently_linear F hF b L hb hL1 c' hc'
    (H _ hslope)
  refine ⟨j,hL1.trans (mem_Icc.mp hj).1,Hj.mono ?_⟩
  intro m hm
  exact (mul_le_mul_of_nonneg_right (le_max_right 0 c) (Nat.cast_nonneg _)).trans_lt hm

/-- A single multiplier works at cofinally many progression scales. -/
theorem exists_fixed_mangoldt_geometric_lower (b : ℕ) (hb : 1 < b) (c : ℝ) (hc : c < 1) :
    ∃ j : ℕ, 1 ≤ j ∧ ∃ᶠ m : ℕ in atTop,
      c*(j*b^m : ℕ) < mangoldtSum (j*b^m) :=
  exists_fixed_geometric_grid_unit_lower mangoldtSum mangoldtSum_mono
    frequently_mangoldtSum_gt_linear b hb c hc

end Erdos821
