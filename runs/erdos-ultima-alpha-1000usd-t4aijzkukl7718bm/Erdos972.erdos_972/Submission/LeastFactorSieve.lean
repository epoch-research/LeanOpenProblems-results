import Submission.CappedLowerSieve

/-! Upper sieve bounds for weighted least-prime-factor logarithms.
The divisor-row errors are explicit hypotheses, not discarded terms. -/
namespace Erdos972LeastFactorSieve

open Finset ArithmeticFunction
open Erdos972SelbergWeights Erdos972PairSieve Erdos972SelbergLowerTest
open Erdos972CappedLowerSieve Erdos972SieveMassLower

noncomputable def roughWeight (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ) (R : ℕ) : ℝ :=
  ∑ n ∈ S, if (g n).Coprime R.factorial then a n else 0

lemma roughWeight_nonneg (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ) (R : ℕ)
    (ha : ∀ n ∈ S, 0 ≤ a n) : 0 ≤ roughWeight S a g R := by
  apply sum_nonneg
  intro n hn
  split_ifs
  · exact ha n hn
  · exact le_rfl

lemma majorant_eq_one_of_coprime {R n : ℕ} (hR : 1 ≤ R)
    (hc : n.Coprime R.factorial) : majorant R n = 1 := by
  have hh : (∑ d ∈ Ioc 0 R, if d ∣ n then selbergWeight R d else 0) = 1 := by
    rw [sum_eq_single 1]
    · simp only [one_dvd, if_true, selbergWeight_one hR]
    · intro d hd hd1
      apply if_neg
      intro hdn
      exact hd1 (Nat.eq_one_of_dvd_coprimes hc hdn
        (Nat.dvd_factorial (mem_Ioc.mp hd).1 (mem_Ioc.mp hd).2))
    · intro h
      exact (h (mem_Ioc.mpr ⟨by omega, hR⟩)).elim
  simp only [majorant, hh, one_pow]

/-- The rough-output upper bound has quadratic, rather than quartic,
Selberg coefficient error. -/
theorem rough_weight_upper (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    (ha : ∀ n ∈ S, 0 ≤ a n) {R : ℕ} (hR : 1 ≤ R)
    {X E : ℝ} (hE : 0 ≤ E)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ R^2 → |row S a g d-X/d| ≤ E) :
    roughWeight S a g R ≤ X/sieveMass R + E*(R:ℝ)^2 := by
  have hh := moment_error_square S a g (p := 1) hR hE (fun z hz => by
    rw [Nat.lcm_one_right]
    exact hrows _ (weightDivisor_bounds hz).1 (weightDivisor_bounds hz).2)
  rw [localMain_one hR, mul_one_div] at hh
  have hm : moment S a g R 1 ≤ X/sieveMass R + E*(R:ℝ)^2 := by
    linarith only [(abs_le.mp hh).2]
  apply le_trans _ hm
  unfold roughWeight moment
  simp only [one_dvd, if_true]
  apply sum_le_sum
  intro n hn
  split_ifs with hc
  · rw [majorant_eq_one_of_coprime hR hc, mul_one]
  · exact mul_nonneg (ha n hn) (majorant_nonneg _ _)

lemma log_sieveMass_bound {R : ℕ} (hR : 2 ≤ R) :
    Real.log R ≤ 2*sieveMass R := by
  apply le_trans _ (log_le_two_sieveMass R)
  exact Real.log_le_log (by exact_mod_cast (show 0 < R by omega)) (by norm_num)

/-- Multiplying by the cutoff logarithm makes the main term uniform. -/
theorem log_mul_rough_weight_upper (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    (ha : ∀ n ∈ S, 0 ≤ a n) {R : ℕ} (hR : 2 ≤ R)
    {X E : ℝ} (hX : 0 ≤ X) (hE : 0 ≤ E)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ R^2 → |row S a g d-X/d| ≤ E) :
    Real.log R * roughWeight S a g R ≤ 2*X + E*(R:ℝ)^2*Real.log R := by
  have hG : 0 < sieveMass R := lt_of_lt_of_le (by norm_num)
    (one_le_sieveMass (show 1 ≤ R by omega))
  have hh := mul_le_mul_of_nonneg_left
    (rough_weight_upper S a g ha (show 1 ≤ R by omega) hE hrows)
    (Real.log_natCast_nonneg R)
  have hb : Real.log R*(X/sieveMass R) ≤ 2*X := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hG).mpr
    have h := mul_le_mul_of_nonneg_left (log_sieveMass_bound hR) hX
    convert h using 1 <;> ring
  nlinarith only [hh, hb]

/-- A finite logarithmic layer bound. The final tail is retained explicitly. -/
lemma layer_bound (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {y L : ℝ}
    (hy : y ≤ L) (hL : 0 ≤ L) (J : ℕ) :
    y ≤ b 0 + (∑ j ∈ range J, if b j < y then b (j+1) else 0) +
      (if b J < y then L else 0) := by
  have hsum (K : ℕ) : 0 ≤ ∑ j ∈ range K, if b j < y then b (j+1) else 0 := by
    apply sum_nonneg
    intro j hj
    split_ifs
    · exact hb _
    · exact le_rfl
  induction J with
  | zero =>
    simp only [range_zero, sum_empty, add_zero]
    split_ifs with h
    · linarith only [hy, hb 0]
    · simpa only [add_zero] using (le_of_not_gt h)
  | succ J ih =>
    rw [sum_range_succ]
    by_cases hj : b J < y
    · rw [if_pos hj]
      split_ifs with hk
      · linarith only [hy, hb 0, hb (J+1), hsum J]
      · have hyl : y ≤ b (J+1) := le_of_not_gt hk
        linarith only [hyl, hb 0, hsum J]
    · rw [if_neg hj, add_zero] at *
      split_ifs
      · linarith only [ih, hL]
      · simpa only [add_zero] using ih

/-- Sieve cutoffs with exactly doubling logarithms. -/
def logLevel (j : ℕ) : ℕ := 2^(2^j)

lemma logLevel_two_le (j : ℕ) : 2 ≤ logLevel j := by
  exact Nat.le_pow (by positivity : 0 < 2^j)

lemma logLevel_mono : Monotone logLevel := by
  intro i j hij
  exact Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hij)

lemma log_logLevel (j : ℕ) : Real.log (logLevel j) = (2:ℝ)^j*Real.log 2 := by
  simp only [logLevel, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

lemma log_logLevel_succ (j : ℕ) : Real.log (logLevel (j+1)) = 2*Real.log (logLevel j) := by
  rw [log_logLevel, log_logLevel, pow_succ]
  ring

lemma log_logLevel_pos (j : ℕ) : 0 < Real.log (logLevel j) :=
  Real.log_pos (Nat.one_lt_cast.mpr (logLevel_two_le j))

lemma logLevel_zero : logLevel 0 = 2 := by simp [logLevel]

lemma log_minFac_lt_iff {R n : ℕ} (hR : 0 < R) :
    Real.log R < Real.log n.minFac ↔ R < n.minFac := by
  rw [Real.log_lt_log_iff (Nat.cast_pos.mpr hR) (Nat.cast_pos.mpr (Nat.minFac_pos n)), Nat.cast_lt]

/-- The layer decomposition converts a least-factor moment into rough-output
counts at a finite family of cutoffs. -/
theorem weighted_least_factor_layers (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    (ha : ∀ n ∈ S, 0 ≤ a n) {L : ℝ} (hL : 0 ≤ L)
    (hy : ∀ n ∈ S, Real.log (g n).minFac ≤ L) (J : ℕ) :
    (∑ n ∈ S, a n * Real.log (g n).minFac) ≤
      Real.log 2 * (∑ n ∈ S, a n) +
        (∑ j ∈ range J, Real.log (logLevel (j+1)) * roughWeight S a g (logLevel j)) +
        L * roughWeight S a g (logLevel J) := by
  classical
  have hlocal (n : ℕ) (hn : n ∈ S) :
      Real.log (g n).minFac ≤ Real.log 2 +
        (∑ j ∈ range J, if (g n).Coprime (logLevel j).factorial then
          Real.log (logLevel (j+1)) else 0) +
        (if (g n).Coprime (logLevel J).factorial then L else 0) := by
    by_cases hn1 : g n = 1
    · simp only [hn1, Nat.minFac_one, Nat.cast_one, Real.log_one]
      positivity [Real.log_natCast_nonneg]
    · have hh := layer_bound (fun j => Real.log (logLevel j))
        (fun j => (log_logLevel_pos j).le) (hy n hn) hL J
      have hi (j : ℕ) :
          (Real.log (logLevel j) < Real.log (g n).minFac) ↔
            (g n).Coprime (logLevel j).factorial :=
        (log_minFac_lt_iff (show 0 < logLevel j by have := logLevel_two_le j; omega)).trans
          (Nat.coprime_factorial_iff hn1).symm
      simpa only [hi, logLevel_zero, Nat.cast_ofNat] using hh
  apply (sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left (hlocal n hn) (ha n hn))).trans_eq
  simp only [mul_add, sum_add_distrib, mul_sum, roughWeight]
  congr 1
  · congr 1
    · apply sum_congr rfl
      intro n hn
      ring
    · rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      apply sum_congr rfl
      intro n hn
      split_ifs <;> ring
  · apply sum_congr rfl
    intro n hn
    split_ifs <;> ring

noncomputable def leastFactorBudget (X E L : ℝ) (J : ℕ) : ℝ :=
  Real.log 2*(X+E) + 4*X*J + 2*X*L/Real.log (logLevel J) +
    E*(logLevel J : ℝ)^2*(2*J*Real.log (logLevel J)+L)

/-- An explicit upper bound for the least-factor logarithm using only rows
up to the square of the largest sieve cutoff. The number of logarithmic
layers, rather than the input logarithm itself, enters the main term. -/
theorem weighted_least_factor_upper (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    (ha : ∀ n ∈ S, 0 ≤ a n) {X E L : ℝ}
    (hX : 0 ≤ X) (hE : 0 ≤ E) (hL : 0 ≤ L)
    (hy : ∀ n ∈ S, Real.log (g n).minFac ≤ L) (J : ℕ)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ (logLevel J)^2 →
      |row S a g d-X/d| ≤ E) :
    (∑ n ∈ S, a n * Real.log (g n).minFac) ≤ leastFactorBudget X E L J := by
  let Z := logLevel J
  have hZ : 2 ≤ Z := logLevel_two_le J
  have hlogZ : 0 < Real.log Z := log_logLevel_pos J
  have hsum : (∑ n ∈ S, a n) ≤ X+E := by
    have hh := hrows 1 (by omega) (one_le_pow₀ (show 1 ≤ logLevel J by have := logLevel_two_le J; omega))
    simp only [row, one_dvd, if_true, Nat.cast_one, div_one] at hh
    linarith only [(abs_le.mp hh).2]
  have hr (j : ℕ) (hj : j ≤ J) :
      Real.log (logLevel j)*roughWeight S a g (logLevel j) ≤
        2*X + E*(Z:ℝ)^2*Real.log Z := by
    have hRZ := logLevel_mono hj
    have hh := log_mul_rough_weight_upper S a g ha (logLevel_two_le j) hX hE
      (fun d hd hdR => hrows d hd (hdR.trans (Nat.pow_le_pow_left hRZ 2)))
    apply hh.trans
    gcongr
    exact_mod_cast (show 0 < logLevel j by have := logLevel_two_le j; omega)
  have hmiddle :
      (∑ j ∈ range J, Real.log (logLevel (j+1))*roughWeight S a g (logLevel j)) ≤
        (J:ℝ)*(4*X+2*E*(Z:ℝ)^2*Real.log Z) := by
    calc
      _ ≤ ∑ j ∈ range J, (4*X+2*E*(Z:ℝ)^2*Real.log Z) := by
        apply sum_le_sum
        intro j hj
        rw [log_logLevel_succ]
        have hh := mul_le_mul_of_nonneg_left (hr j (Nat.le_of_lt (mem_range.mp hj)))
          (by norm_num : (0:ℝ) ≤ 2)
        nlinarith only [hh]
      _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]
  have htail : L*roughWeight S a g Z ≤ 2*X*L/Real.log Z + E*(Z:ℝ)^2*L := by
    have hh := hr J le_rfl
    change Real.log Z*roughWeight S a g Z ≤ _ at hh
    have hd : roughWeight S a g Z ≤ 2*X/Real.log Z + E*(Z:ℝ)^2 := by
      rw [mul_comm (Real.log Z)] at hh
      have hd := (le_div_iff₀ hlogZ).mpr hh
      simpa only [add_div, mul_div_cancel_right₀ _ hlogZ.ne'] using hd
    have hm := mul_le_mul_of_nonneg_left hd hL
    convert hm using 1; ring
  apply (weighted_least_factor_layers S a g ha hL hy J).trans
  have hb := mul_le_mul_of_nonneg_left hsum (Real.log_natCast_nonneg 2)
  change Real.log 2*(∑ n ∈ S, a n) ≤ Real.log 2*(X+E) at hb
  have hh := add_le_add (add_le_add hb hmiddle) htail
  apply hh.trans_eq
  dsimp only [leastFactorBudget, Z]
  ring

lemma leastFactorBudget_linear {X E L N : ℝ} (J : ℕ)
    (hN : 0 ≤ N) (hX : 0 ≤ X) (hE : 0 ≤ E)
    (hXup : X ≤ 7*N) (hEup : E*(logLevel J : ℝ)^4 ≤ N)
    (hLup : L ≤ 5000*Real.log (logLevel J)) :
    leastFactorBudget X E L J ≤ 100000*N*(J+1) := by
  let Z := (logLevel J : ℝ)
  have hZ : 1 ≤ Z := by dsimp [Z]; exact_mod_cast (show 1 ≤ logLevel J by have := logLevel_two_le J; omega)
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hlogZ : 0 < Real.log Z := log_logLevel_pos J
  have hlog : Real.log Z ≤ Z^2 := by
    have hh := Real.log_le_sub_one_of_pos hZ0
    nlinarith only [hh, hZ, sq_nonneg (Z-1)]
  have hEN : E ≤ N := (le_mul_of_one_le_right hE (one_le_pow₀ hZ)).trans hEup
  have hfirst : Real.log 2*(X+E) ≤ 8*N := by
    have hl : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
    have hh := mul_le_mul_of_nonneg_right hl (add_nonneg hX hE)
    nlinarith only [hh, hXup, hEN]
  have hsecond : 4*X*(J:ℝ) ≤ 28*N*J := by
    have hh := mul_le_mul_of_nonneg_right hXup (show 0 ≤ 4*(J:ℝ) by positivity)
    nlinarith only [hh]
  have hthird : 2*X*L/Real.log Z ≤ 70000*N := by
    have hlo : L/Real.log Z ≤ 5000 := (div_le_iff₀ hlogZ).mpr hLup
    have hh := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 2*X by positivity)
    have hx := mul_le_mul_of_nonneg_left hXup (by norm_num : (0:ℝ) ≤ 10000)
    calc
      _ = 2*X*(L/Real.log Z) := by ring
      _ ≤ 2*X*5000 := hh
      _ ≤ _ := by nlinarith only [hx]
  have hfourth : E*Z^2*(2*(J:ℝ)*Real.log Z+L) ≤ N*(2*J+5000) := by
    have h₁ := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2*(J:ℝ)+5000 by positivity)
    have hlo : 2*(J:ℝ)*Real.log Z+L ≤ (2*J+5000)*Z^2 := by
      nlinarith only [h₁, hLup]
    have h₂ := mul_le_mul_of_nonneg_left hlo (show 0 ≤ E*Z^2 by positivity)
    have h₃ := mul_le_mul_of_nonneg_right hEup (show 0 ≤ 2*(J:ℝ)+5000 by positivity)
    calc
      _ ≤ E*Z^2*((2*J+5000)*Z^2) := h₂
      _ = (E*Z^4)*(2*J+5000) := by ring
      _ ≤ _ := h₃
  have hsum := add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth
  change leastFactorBudget X E L J ≤ _ at hsum
  apply hsum.trans
  have hj : 0 ≤ (J:ℝ) := Nat.cast_nonneg J
  nlinarith only [hN, mul_nonneg hN hj]

#print axioms rough_weight_upper
#print axioms weighted_least_factor_layers
#print axioms weighted_least_factor_upper
#print axioms leastFactorBudget_linear

end Erdos972LeastFactorSieve
