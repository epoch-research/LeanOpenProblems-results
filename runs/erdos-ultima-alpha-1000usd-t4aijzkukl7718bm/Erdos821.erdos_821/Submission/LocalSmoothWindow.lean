import Submission.LocalSmoothBudget
import Submission.Valuation

/-!
# Concentrating the local smooth-predecessor mass

The relevant smooth divisors of a large fiber can be restricted to a finite
window with upper endpoint tau(n)^2. This endpoint is subpower in n. No
multiplicity exponent increase is asserted.
-/

open Nat Filter
open scoped Classical BigOperators

namespace Erdos821

set_option maxHeartbeats 2000000

noncomputable def smoothShiftedDivisorWindow (k n L U : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => d ∈ smoothShiftedPredecessors k ∧ L < d ∧ d ≤ U)

lemma localSmoothMass_le_window (k n L U : ℕ) (hL : 0 < L) (hU : 0 < U)
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) :
    localSmoothMass k n s ≤ (L : ℝ)^(1-s)/(1-s) +
      (smoothShiftedDivisorWindow k n L U).card * (L : ℝ)^(-s) +
      (n.divisors.card : ℝ)*(U : ℝ)^(-s) := by
  let D := n.divisors.filter (fun d => d ∈ smoothShiftedPredecessors k)
  let E := D.filter (fun d => ¬d ≤ L)
  have hsmall : (∑ d ∈ D.filter (fun d => d ≤ L), (d : ℝ)^(-s)) ≤
      (L : ℝ)^(1-s)/(1-s) := by
    apply le_trans _ (sum_Icc_neg_rpow_le L s hs hs1)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hdD, hdL⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_Icc.mpr
        ⟨Nat.pos_of_mem_divisors (Finset.mem_filter.mp hdD).1, hdL⟩
    · intro d hd hdD
      exact Real.rpow_nonneg (Nat.cast_nonneg d) _
  have hwindow : E.filter (fun d => d ≤ U) = smoothShiftedDivisorWindow k n L U := by
    ext d
    simp [E, D, smoothShiftedDivisorWindow, and_assoc]
  have hmiddle : (∑ d ∈ E.filter (fun d => d ≤ U), (d : ℝ)^(-s)) ≤
      (smoothShiftedDivisorWindow k n L U).card * (L : ℝ)^(-s) := by
    rw [hwindow]
    calc
      _ ≤ ∑ _d ∈ smoothShiftedDivisorWindow k n L U, (L : ℝ)^(-s) := by
        apply Finset.sum_le_sum
        intro d hd
        have hLd := (Finset.mem_filter.mp hd).2.2.1
        exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hL)
          (by exact_mod_cast hLd.le) (neg_nonpos.mpr hs)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have htail : (∑ d ∈ E.filter (fun d => ¬d ≤ U), (d : ℝ)^(-s)) ≤
      (n.divisors.card : ℝ)*(U : ℝ)^(-s) := by
    have hsub : E.filter (fun d => ¬d ≤ U) ⊆ n.divisors := by
      intro d hd
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1).1
    calc
      _ ≤ ∑ _d ∈ E.filter (fun d => ¬d ≤ U), (U : ℝ)^(-s) := by
        apply Finset.sum_le_sum
        intro d hd
        have hUd : U < d := Nat.lt_of_not_ge (Finset.mem_filter.mp hd).2
        exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hU)
          (by exact_mod_cast hUd.le) (neg_nonpos.mpr hs)
      _ ≤ ∑ _d ∈ n.divisors, (U : ℝ)^(-s) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun d _ _ => Real.rpow_nonneg (Nat.cast_nonneg U) _)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hE : (∑ d ∈ E, (d : ℝ)^(-s)) ≤
      (smoothShiftedDivisorWindow k n L U).card * (L : ℝ)^(-s) +
      (n.divisors.card : ℝ)*(U : ℝ)^(-s) := by
    rw [← Finset.sum_filter_add_sum_filter_not E (fun d => d ≤ U)]
    exact add_le_add hmiddle htail
  change (∑ d ∈ D, (d : ℝ)^(-s)) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not D (fun d => d ≤ L)]
  exact (add_le_add hsmall hE).trans_eq (add_assoc _ _ _).symm

lemma divisor_square_cutoff_cost_le_one (n : ℕ) (hn : 0 < n)
    (s : ℝ) (hs : 1/2 ≤ s) :
    (n.divisors.card : ℝ)*((n.divisors.card^2 : ℕ) : ℝ)^(-s) ≤ 1 := by
  have hτ : 1 ≤ n.divisors.card := Finset.card_pos.mpr
    ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩
  have hτR : (1 : ℝ) ≤ n.divisors.card := by exact_mod_cast hτ
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity)]
  norm_num only [Nat.cast_ofNat]
  calc
    _ ≤ (n.divisors.card : ℝ)*(n.divisors.card : ℝ)^(-1 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hτR (by linarith)) (Nat.cast_nonneg _)
    _ = 1 := by rw [Real.rpow_neg_one, mul_inv_cancel₀ (by linarith)]

/-- The mass outside the divisor-square window costs at most one. -/
theorem localSmoothMass_endpoint_le_window (k : ℕ) (hk : 2 ≤ k)
    (n : ℕ) (hn : 0 < n) (B : ℕ) (hB : 0 < B) :
    localSmoothMass k n (1-1/(k : ℝ)) ≤ (k : ℝ)*B +
      (smoothShiftedDivisorWindow k n (B^k) (n.divisors.card^2)).card *
        ((B : ℝ)^(k-1))⁻¹ + 1 := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hτ : 0 < n.divisors.card := Finset.card_pos.mpr
    ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩
  have hb := reciprocal_exponent_bounds k hk1
  have hs : (1/2 : ℝ) ≤ 1-1/(k : ℝ) := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ k by exact_mod_cast hk)
    linarith
  have hc := localSmoothMass_le_window k n (B^k) (n.divisors.card^2)
    (pow_pos hB k) (pow_pos hτ 2) (1-1/(k : ℝ)) hb.1 hb.2
  have htail := divisor_square_cutoff_cost_le_one n hn (1-1/(k : ℝ)) hs
  have hcost : ((B^k : ℕ) : ℝ)^(1-(1-1/(k : ℝ)))/(1-(1-1/(k : ℝ))) =
      (k : ℝ)*B := by
    have he : (k : ℝ)*(1-(1-1/(k : ℝ))) = 1 := by field_simp; ring
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul hBR.le, he, Real.rpow_one,
      sub_sub_cancel]
    field_simp
  have hweight : ((B^k : ℕ) : ℝ)^(-(1-1/(k : ℝ))) = ((B : ℝ)^(k-1))⁻¹ := by
    have he : (k : ℝ)*(-(1-1/(k : ℝ))) = -((k-1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk1, Nat.cast_one]
      field_simp
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul hBR.le, he, Real.rpow_neg hBR.le,
      Real.rpow_natCast]
  rw [hcost, hweight] at hc
  linarith

/-- The upper endpoint of the window is smaller than every fixed power of n. -/
theorem eventually_divisor_square_cutoff_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ((n.divisors.card^2 : ℕ) : ℝ) ≤ (n : ℝ)^ε := by
  filter_upwards [eventually_card_divisors_le_rpow (ε/2) (half_pos hε)] with n hn
  calc
    _ ≤ ((n : ℝ)^(ε/2))^2 := by
      rw [Nat.cast_pow]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hn 2
    _ = _ := by rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]; congr 1; norm_num

/-- A large fiber has polynomially many smooth shifted divisors in log n
inside a window whose upper endpoint is subpower in n. -/
theorem eventually_large_g_forces_many_smooth_divisors_in_window
    (k : ℕ) (hk : 2 ≤ k) (γ : ℝ) (hγ : 1-1/(k : ℝ) < γ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (n : ℝ)^γ < g n → C*(Real.log n)^k <
        (smoothShiftedDivisorWindow k n (⌊c*Real.log n⌋₊^k) (n.divisors.card^2)).card := by
  let Δ := γ-(1-1/(k : ℝ))
  let c := Δ/(16*(k : ℝ))
  let C := (Δ/8)*(c/2)^(k-1)
  have hΔ : 0 < Δ := sub_pos.mpr hγ
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hc : 0 < c := div_pos hΔ (by positivity)
  have hC : 0 < C := by dsimp [C]; positivity
  have hkc : (k : ℝ)*c = Δ/16 := by dsimp [c]; field_simp
  refine ⟨c, C, hc, hC, ?_⟩
  have hlim : Tendsto (fun n : ℕ => c*Real.log n) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  filter_upwards [eventually_large_g_forces_local_smooth_mass k (by omega) γ hγ,
    hlim.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with n hn hscale hn1
  intro hg
  let B := ⌊c*Real.log n⌋₊
  have hB2 : 2 ≤ B := Nat.le_floor hscale
  have hB : 0 < B := by omega
  have hlog : 0 < Real.log n := by nlinarith
  have hBle : (B : ℝ) ≤ c*Real.log n := Nat.floor_le (by positivity)
  have hBlt : c*Real.log n < (B : ℝ)+1 := Nat.lt_floor_add_one _
  have hBge : (c/2)*Real.log n ≤ B := by nlinarith
  have hlocal := hn hg
  change (Δ/4)*Real.log n < _ at hlocal
  have hcut := localSmoothMass_endpoint_le_window k hk n (by omega) B hB
  have hcost : (k : ℝ)*B ≤ (Δ/16)*Real.log n := by
    calc
      _ ≤ (k : ℝ)*(c*Real.log n) := mul_le_mul_of_nonneg_left hBle hkR.le
      _ = _ := by rw [← mul_assoc, hkc]
  have hunit : 1 ≤ (Δ/16)*Real.log n := by
    calc
      1 ≤ (k : ℝ)*2 := by
        have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      _ ≤ (k : ℝ)*(c*Real.log n) := mul_le_mul_of_nonneg_left hscale hkR.le
      _ = _ := by rw [← mul_assoc, hkc]
  have htail : (Δ/8)*Real.log n <
      (smoothShiftedDivisorWindow k n (B^k) (n.divisors.card^2)).card * ((B : ℝ)^(k-1))⁻¹ := by
    linarith
  have hBp : (0 : ℝ) < (B : ℝ)^(k-1) := pow_pos (by exact_mod_cast hB) _
  have hcount : ((Δ/8)*Real.log n)*(B : ℝ)^(k-1) <
      (smoothShiftedDivisorWindow k n (B^k) (n.divisors.card^2)).card := by
    have h := mul_lt_mul_of_pos_right htail hBp
    simpa only [mul_assoc, inv_mul_cancel₀ hBp.ne', mul_one] using h
  apply lt_of_le_of_lt _ hcount
  have hp := pow_le_pow_left₀ (show 0 ≤ (c/2)*Real.log n by positivity) hBge (k-1)
  have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ (Δ/8)*Real.log n by positivity)
  convert h using 1
  dsimp [C]
  have he : (Real.log n)^k = (Real.log n)^(k-1)*Real.log n := by
    rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ k by omega)]
  rw [mul_pow, he]
  ring


end Erdos821
