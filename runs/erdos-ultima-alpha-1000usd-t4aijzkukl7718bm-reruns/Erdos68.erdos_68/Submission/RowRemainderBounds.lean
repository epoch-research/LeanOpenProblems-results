import Submission.RowwiseFloors
import Submission.FactorialLambert
import Submission.FactorialClearingIndex

/-!
Arithmetic bounds for the fractional remainders of the individual rows.
These are auxiliary estimates, not a proof of the conjecture in Spec.lean.
-/

namespace RowRemainderBounds

open Erdos68Development

/-- Multinomial divisibility lets us remove an integer geometric prefix. -/
lemma row_fraction_le_geometric_tail (n k j : ℕ) (hk : 2 ≤ k) (hj : j * k ≤ n) :
    (n.factorial : ℝ) / (k.factorial - 1 : ℝ) -
        ⌊(n.factorial : ℝ) / (k.factorial - 1 : ℝ)⌋ ≤
      (n.factorial : ℝ) / ((k.factorial : ℝ) ^ j * (k.factorial - 1)) := by
  have hdf : (k.factorial : ℝ) ≠ 0 := by positivity
  have htwo : 2 ≤ k.factorial := by
    simpa using Nat.factorial_le hk
  have hd : (0 : ℝ) < k.factorial - 1 := by
    have h : (2 : ℝ) ≤ k.factorial := by exact_mod_cast htwo
    linarith
  have hdiv : k.factorial ^ j ∣ n.factorial :=
    (factorial_pow_dvd_factorial_mul k j).trans
      (Nat.factorial_dvd_factorial (by simpa [Nat.mul_comm] using hj))
  let q : ℕ := n.factorial / k.factorial ^ j
  let s : ℕ := ∑ i ∈ Finset.range j, k.factorial ^ i
  have hq : (q : ℝ) = (n.factorial : ℝ) / (k.factorial : ℝ) ^ j := by
    dsimp [q]
    rw [Nat.cast_div hdiv (by positivity), Nat.cast_pow]
  have hs : (s : ℝ) * (k.factorial - 1 : ℝ) = (k.factorial : ℝ) ^ j - 1 := by
    dsimp [s]
    push_cast
    exact geom_sum_mul (k.factorial : ℝ) j
  have he : (n.factorial : ℝ) / (k.factorial - 1 : ℝ) =
      ((q * s : ℕ) : ℝ) +
        (n.factorial : ℝ) / ((k.factorial : ℝ) ^ j * (k.factorial - 1)) := by
    rw [Nat.cast_mul, hq]
    field_simp
    nlinarith [hs]
  have hlo : ((q * s : ℕ) : ℝ) ≤ (n.factorial : ℝ) / (k.factorial - 1 : ℝ) := by
    rw [he]
    have : 0 ≤ (n.factorial : ℝ) / ((k.factorial : ℝ) ^ j * (k.factorial - 1)) :=
      div_nonneg (by positivity) (mul_nonneg (by positivity) hd.le)
    linarith
  have hf : (q * s : ℤ) ≤ ⌊(n.factorial : ℝ) / (k.factorial - 1 : ℝ)⌋ := by
    apply Int.le_floor.mpr
    exact_mod_cast hlo
  have hf' : ((q * s : ℕ) : ℝ) ≤
      (⌊(n.factorial : ℝ) / (k.factorial - 1 : ℝ)⌋ : ℝ) := by
    exact_mod_cast hf
  linarith

/-- Away from a band immediately preceding a multiple of k, a factorial
power exceeds n! by an exponential factor. The large threshold is deliberate:
only elementary natural-number inequalities are used. -/
lemma factorial_power_large (n k C J L : ℕ)
    (hL : 0 < L) (hk : k ≤ n) (hC : C ≤ J)
    (hn : 2 ^ (L * (J ^ 2 + 1)) ≤ n)
    (hgap : n / L < C * k - n) :
    n.factorial * 2 ^ n ≤ k.factorial ^ C := by
  have hslack : n < L * (C * k - n) := by
    simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hL).mp hgap
  have hkn : n ≤ C * k := by
    have : 0 < C * k - n := lt_of_le_of_lt (Nat.zero_le _) hgap
    omega
  have hlo := @Nat.factorial_mul_pow_le_factorial n (C * k - n)
  rw [Nat.add_sub_of_le hkn] at hlo
  have hu : (C * k).factorial ≤ 2 ^ (C ^ 2 * k) * k.factorial ^ C := by
    rw [← FactorialClearingIndex.blockCoefficient_identity]
    exact Nat.mul_le_mul_right _ (FactorialClearingIndex.blockCoefficient_bound C k)
  have he : C ^ 2 * k + n ≤ L * (J ^ 2 + 1) * (C * k - n) := by
    have hc2 : C ^ 2 ≤ J ^ 2 := Nat.pow_le_pow_left hC 2
    have hprod : C ^ 2 * k ≤ J ^ 2 * n := Nat.mul_le_mul hc2 hk
    have hmul := Nat.mul_le_mul_left (J ^ 2 + 1) hslack.le
    nlinarith
  have hp : 2 ^ (C ^ 2 * k + n) ≤ (n + 1) ^ (C * k - n) := by
    calc
      2 ^ (C ^ 2 * k + n) ≤ 2 ^ (L * (J ^ 2 + 1) * (C * k - n)) :=
        Nat.pow_le_pow_right (by omega) he
      _ = (2 ^ (L * (J ^ 2 + 1))) ^ (C * k - n) := pow_mul _ _ _
      _ ≤ (n + 1) ^ (C * k - n) := Nat.pow_le_pow_left (by omega) _
  have h := (Nat.mul_le_mul_left n.factorial hp).trans (hlo.trans hu)
  rw [pow_add] at h
  have hh : 2 ^ (C ^ 2 * k) * (n.factorial * 2 ^ n) ≤
      2 ^ (C ^ 2 * k) * k.factorial ^ C := by nlinarith [h]
  exact Nat.le_of_mul_le_mul_left hh (by positivity)

/-- The fractional contribution of a row outside the exceptional bands is tiny. -/
lemma row_fraction_small (n k J L : ℕ)
    (hJpos : 0 < J) (hL : 0 < L) (hk2 : 2 ≤ k) (hkn : k ≤ n) (hJ : n / J < k)
    (hn : 2 ^ (L * (J ^ 2 + 1)) ≤ n)
    (hgap : n / L < (n / k + 1) * k - n) :
    (n.factorial : ℝ) / (k.factorial - 1 : ℝ) -
        ⌊(n.factorial : ℝ) / (k.factorial - 1 : ℝ)⌋ ≤
      2 / (2 : ℝ) ^ n := by
  have hC : n / k + 1 ≤ J := by
    have h1 := (Nat.div_lt_iff_lt_mul hJpos).mp hJ
    have h2 : n / k < J := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by nlinarith)
    omega
  have hpow := factorial_power_large n k (n / k + 1) J L hL hkn hC hn hgap
  have hpowR : (n.factorial : ℝ) * (2 : ℝ) ^ n ≤
      (k.factorial : ℝ) ^ (n / k + 1) := by exact_mod_cast hpow
  have htwo : (2 : ℝ) ≤ k.factorial := by
    exact_mod_cast (show 2 ≤ k.factorial by simpa using Nat.factorial_le hk2)
  have hf : (0 : ℝ) < k.factorial := by positivity
  have hd : (0 : ℝ) < k.factorial - 1 := by linarith
  have hbase := row_fraction_le_geometric_tail n k (n / k) hk2 (Nat.div_mul_le_self n k)
  refine hbase.trans ?_
  apply (div_le_div_iff₀ (mul_pos (pow_pos hf _) hd) (by positivity)).mpr
  have hh : (k.factorial : ℝ) ≤ 2 * (k.factorial - 1) := by linarith
  have hm := mul_le_mul_of_nonneg_left hh (pow_nonneg hf.le (n / k))
  rw [pow_succ] at hpowR
  nlinarith

def transitionBand (n J L : ℕ) : Finset ℕ :=
  (Finset.Ico 2 (n + 1)).filter
    (fun k => n / J < k ∧ (n / k + 1) * k - n ≤ n / L)

lemma transitionBand_card (n J L : ℕ) (hJ : 0 < J) :
    (transitionBand n J L).card ≤ J * (n / L + 1) := by
  let f : ℕ → ℕ × ℕ := fun k => (n / k, (n / k + 1) * k - n)
  have h := Finset.card_le_card_of_injOn (s := transitionBand n J L)
    (t := (Finset.range J) ×ˢ (Finset.range (n / L + 1))) f
  have hm : Set.MapsTo f (transitionBand n J L) ↑((Finset.range J) ×ˢ
      (Finset.range (n / L + 1))) := by
    intro k hk
    change k ∈ transitionBand n J L at hk
    change f k ∈ (Finset.range J) ×ˢ (Finset.range (n / L + 1))
    simp only [transitionBand, Finset.mem_filter, Finset.mem_Ico] at hk
    simp only [f, Finset.mem_product, Finset.mem_range]
    refine ⟨?_, by omega⟩
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).mpr
    have h := (Nat.div_lt_iff_lt_mul hJ).mp hk.2.1
    nlinarith
  have hi : Set.InjOn f (transitionBand n J L) := by
    intro a ha b hb hab
    change a ∈ transitionBand n J L at ha
    change b ∈ transitionBand n J L at hb
    simp only [transitionBand, Finset.mem_filter, Finset.mem_Ico] at ha hb
    have hab1 : n / a = n / b := congrArg Prod.fst hab
    have hab2 : (n / a + 1) * a - n = (n / b + 1) * b - n := congrArg Prod.snd hab
    have haa : n < (n / a + 1) * a := by
      have := (Nat.div_lt_iff_lt_mul (by omega : 0 < a)).mp (Nat.lt_succ_self (n / a))
      exact this
    have hbb : n < (n / b + 1) * b := by
      have := (Nat.div_lt_iff_lt_mul (by omega : 0 < b)).mp (Nat.lt_succ_self (n / b))
      exact this
    have he : (n / a + 1) * a = (n / b + 1) * b := by omega
    rw [← hab1] at he
    exact Nat.eq_of_mul_eq_mul_left (by positivity) he
  simpa using h hm hi

noncomputable def rowRemainder (n k : ℕ) : ℝ :=
  Int.fract ((n.factorial : ℝ) / (k.factorial - 1 : ℝ))

lemma rowRemainder_sum_bound (n J L : ℕ) (hJ : 0 < J) (hL : 0 < L)
    (hn : 2 ^ (L * (J ^ 2 + 1)) ≤ n) :
    (∑ k ∈ Finset.Ico 2 (n + 1), rowRemainder n k) ≤
      (n / J + 1 : ℕ) + (J * (n / L + 1) : ℕ) +
        (n + 1 : ℝ) * (2 / (2 : ℝ) ^ n) := by
  let low := (Finset.Ico 2 (n + 1)).filter (fun k => k ≤ n / J)
  have hlcard : low.card ≤ n / J + 1 := by
    calc
      low.card ≤ (Finset.range (n / J + 1)).card := Finset.card_le_card (by
        intro k hk
        simp only [low, Finset.mem_filter, Finset.mem_Ico] at hk
        simpa only [Finset.mem_range] using (show k < n / J + 1 by omega))
      _ = _ := Finset.card_range _
  have hbcard := transitionBand_card n J L hJ
  have hpoint (k : ℕ) (hk : k ∈ Finset.Ico 2 (n + 1)) :
      rowRemainder n k ≤
        (if k ∈ low then (1 : ℝ) else 0) +
        (if k ∈ transitionBand n J L then (1 : ℝ) else 0) + 2 / (2 : ℝ) ^ n := by
    by_cases hl : k ≤ n / J
    · have hl' : k ∈ low := by simp [low, hk, hl]
      rw [if_pos hl']
      have hb : 0 ≤ (if k ∈ transitionBand n J L then (1 : ℝ) else 0) := by positivity
      have hf : rowRemainder n k < 1 := Int.fract_lt_one _
      have he : 0 ≤ 2 / (2 : ℝ) ^ n := by positivity
      linarith
    · have hl' : k ∉ low := by simp [low, hl]
      rw [if_neg hl']
      by_cases hg : (n / k + 1) * k - n ≤ n / L
      · have hb' : k ∈ transitionBand n J L := by simp [transitionBand, hk]; omega
        rw [if_pos hb']
        have hf : rowRemainder n k < 1 := Int.fract_lt_one _
        have he : 0 ≤ 2 / (2 : ℝ) ^ n := by positivity
        linarith
      · have hb' : k ∉ transitionBand n J L := by
          intro hb
          exact hg ((Finset.mem_filter.mp hb).2.2)
        simp only [if_neg hb', zero_add]
        have hk' := Finset.mem_Ico.mp hk
        exact row_fraction_small n k J L hJ hL hk'.1 (by omega) (by omega) hn (by omega)
  have hs := Finset.sum_le_sum hpoint
  have hlow : (∑ k ∈ Finset.Ico 2 (n + 1), if k ∈ low then (1 : ℝ) else 0) = low.card := by
    rw [← Finset.sum_filter]
    have he : (Finset.Ico 2 (n + 1)).filter (fun k => k ∈ low) = low := by
      ext k
      simp only [Finset.mem_filter, low]
      tauto
    simp [he]
  have hband : (∑ k ∈ Finset.Ico 2 (n + 1),
      if k ∈ transitionBand n J L then (1 : ℝ) else 0) = (transitionBand n J L).card := by
    rw [← Finset.sum_filter]
    have he : (Finset.Ico 2 (n + 1)).filter (fun k => k ∈ transitionBand n J L) =
        transitionBand n J L := by
      ext k
      simp only [transitionBand, Finset.mem_filter]
      tauto
    simp [he]
  simp only [Finset.sum_add_distrib, hlow, hband, Finset.sum_const, nsmul_eq_mul] at hs
  have hc : (Finset.Ico 2 (n + 1)).card ≤ n + 1 := by simp; omega
  have h0 : (low.card : ℝ) ≤ (n / J + 1 : ℕ) := by exact_mod_cast hlcard
  have h1 : ((transitionBand n J L).card : ℝ) ≤ (J * (n / L + 1) : ℕ) := by exact_mod_cast hbcard
  have h2 : ((Finset.Ico 2 (n + 1)).card : ℝ) ≤ n + 1 := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 2 / 2 ^ n)
  linarith

lemma rowRemainder_sum (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.Ico 2 (n + 1), rowRemainder n k) =
      (n.factorial : ℝ) * ∑ k ∈ Finset.range (n - 1), term k - rowFloor n := by
  rw [Finset.sum_Ico_eq_sum_range, show n + 1 - 2 = n - 1 by omega,
    Finset.mul_sum]
  simp only [rowFloor, Int.cast_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [rowRemainder, Int.fract]
  have he : (n.factorial : ℝ) / ((2 + k).factorial - 1 : ℝ) =
      (scaledRow n k : ℝ) := by simp [scaledRow, Nat.add_comm]
  rw [he, Rat.floor_cast, cast_scaledRow]

lemma rowTail_bound (n J L : ℕ) (hn2 : 2 ≤ n) (hJ : 0 < J) (hL : 0 < L)
    (hn : 2 ^ (L * (J ^ 2 + 1)) ≤ n) :
    rowTail n ≤ (n / J + 1 : ℕ) + (J * (n / L + 1) : ℕ) +
      (n + 1 : ℝ) * (2 / (2 : ℝ) ^ n) + 3 / (n + 1) := by
  have he := (scaled_partial_sum_error (n - 1)).2
  rw [show n - 1 + 1 = n by omega] at he
  have he' : ((n - 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  rw [he'] at he
  have hs := rowRemainder_sum_bound n J L hJ hL hn
  rw [rowRemainder_sum n hn2] at hs
  unfold rowTail
  nlinarith

lemma rowTail_normalized_bound (n J L : ℕ) (hn2 : 2 ≤ n) (hJ : 0 < J) (hL : 0 < L)
    (hn : 2 ^ (L * (J ^ 2 + 1)) ≤ n) :
    rowTail n / (n + 1 : ℝ) ≤ 1 / (J : ℝ) + (J : ℝ) / L +
      ((J + 1 : ℝ) / (n + 1) + 2 / (2 : ℝ) ^ n + 3 / (n + 1 : ℝ) ^ 2) := by
  have hb := rowTail_bound n J L hn2 hJ hL hn
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have h0 : ((n / J : ℕ) : ℝ) ≤ (n + 1 : ℝ) / J := by
    exact Nat.cast_div_le.trans (div_le_div_of_nonneg_right (by linarith) hJr.le)
  have h1 : ((n / L : ℕ) : ℝ) ≤ (n + 1 : ℝ) / L := by
    exact Nat.cast_div_le.trans (div_le_div_of_nonneg_right (by linarith) hLr.le)
  push_cast at hb
  have hm := mul_le_mul_of_nonneg_left h1 hJr.le
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
  have he : (1 / (J : ℝ) + (J : ℝ) / L +
      ((J + 1 : ℝ) / (n + 1) + 2 / (2 : ℝ) ^ n + 3 / (n + 1 : ℝ) ^ 2)) *
      (n + 1 : ℝ) =
      (n + 1 : ℝ) / J + 1 + (J : ℝ) * ((n + 1 : ℝ) / L + 1) +
        (n + 1 : ℝ) * (2 / (2 : ℝ) ^ n) + 3 / (n + 1) := by
    field_simp
    ring
  rw [he]
  nlinarith

open Filter
open scoped Topology

lemma normalized_error_tendsto_zero (J : ℕ) :
    Tendsto (fun n : ℕ => (J + 1 : ℝ) / (n + 1) + 2 / (2 : ℝ) ^ n +
      3 / (n + 1 : ℝ) ^ 2) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have h1 := h0.const_mul (J + 1 : ℝ)
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 : ℝ)
  have h3 := (h0.pow 2).const_mul (3 : ℝ)
  convert (h1.add h2).add h3 using 1
  · ext n
    simp only [mul_one_div, div_pow, one_pow]
  · norm_num

/-- The rowwise scaled tail is sublinear. No coefficient congruence is asserted. -/
theorem rowTail_sublinear :
    Tendsto (fun n : ℕ => rowTail n / (n + 1 : ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show 0 < ε / 4 by positivity)
  let J := j + 1
  have hJ : 0 < J := by dsimp [J]; omega
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hj' : 1 / (J : ℝ) < ε / 4 := by simpa [J] using hj
  have hsum : 1 / (J : ℝ) + (J : ℝ) / (J * J : ℕ) < ε / 2 := by
    have he : (J : ℝ) / (J * J : ℕ) = 1 / (J : ℝ) := by
      push_cast
      field_simp
    rw [he]
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((normalized_error_tendsto_zero J).eventually_lt_const (show 0 < ε / 2 by positivity))
  refine ⟨max N (max 2 (2 ^ ((J * J) * (J ^ 2 + 1)))), fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnP : 2 ^ ((J * J) * (J ^ 2 + 1)) ≤ n :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hb := rowTail_normalized_bound n J (J * J) hn2 hJ (by positivity) hnP
  have he := hN n hnN
  have hp : 0 ≤ rowTail n / (n + 1 : ℝ) := div_nonneg (rowTail_pos n).le (by positivity)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hp]
  linarith

lemma rowTail_div_self_tendsto :
    Tendsto (fun n : ℕ => rowTail n / (n : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun n => 2 * (rowTail n / (n + 1 : ℝ))) (Eventually.of_forall (fun n =>
    div_nonneg (rowTail_pos n).le (Nat.cast_nonneg n)))
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hp : 0 < rowTail n := rowTail_pos n
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < n)).mpr
    have he : 2 * (rowTail n / (n + 1 : ℝ)) * n = (2 * rowTail n * n) / (n + 1) := by ring
    rw [he]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
    nlinarith
  · simpa using rowTail_sublinear.const_mul (2 : ℝ)

lemma rowCoeff_residue_of_rational (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ))
    (n : ℕ) (hn3 : 3 ≤ n) (hnq : q.den < n) :
    ((rowCoeff n % (n : ℤ) : ℤ) : ℝ) / n = 1 - rowTail n / n := by
  have hqle : q.den ≤ n - 1 := by omega
  obtain ⟨c, hc⟩ := Nat.dvd_factorial q.pos hqle
  let z : ℤ := q.num * (c : ℤ)
  have hz : (n.factorial : ℝ) * (q : ℝ) = (n : ℝ) * (z : ℝ) := by
    have he : n = (n - 1) + 1 := by omega
    conv_lhs => rw [he, Nat.factorial_succ, hc]
    rw [← he, Rat.cast_def]
    dsimp [z]
    push_cast
    have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    field_simp
  let t : ℤ := (n : ℤ) * z - rowFloor n
  have ht : (t : ℝ) = rowTail n := by
    simp only [t, Int.cast_sub, Int.cast_mul, Int.cast_natCast, rowTail, hq, hz]
  have hsmall := rowTail_small hn3
  have ht0 : 0 < t := by exact_mod_cast (show (0 : ℝ) < t by rw [ht]; exact hsmall.1)
  have htn : t < n := by
    have h : (t : ℝ) < n := by rw [ht]; linarith [hsmall.2]
    exact_mod_cast h
  have hcoeff : rowCoeff n = (n : ℤ) * (z - rowFloor (n - 1) - 1) + ((n : ℤ) - t) := by
    have he : n = (n - 1) + 1 := by omega
    conv_lhs => rw [he, rowCoeff]
    rw [← he]
    dsimp [t]
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    ring
  have hmod : rowCoeff n % (n : ℤ) = (n : ℤ) - t := by
    rw [hcoeff, Int.add_emod]
    simp only [Int.mul_emod, Int.emod_self, Int.zero_mul, Int.zero_emod, zero_add,
      Int.emod_emod]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [hmod]
  push_cast
  rw [ht]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

/-- A necessary finite-arithmetic asymptotic condition for rationality.
The failure of this limit for the actual coefficients is not established here. -/
theorem rowCoeff_residue_tendsto_one_of_rational (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) :
    Tendsto (fun n : ℕ => ((rowCoeff n % (n : ℤ) : ℤ) : ℝ) / n) atTop (𝓝 1) := by
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub rowTail_div_self_tendsto
  have he : ∀ᶠ n : ℕ in atTop,
      (1 - rowTail n / n) = ((rowCoeff n % (n : ℤ) : ℤ) : ℝ) / n := by
    filter_upwards [eventually_ge_atTop (max 3 (q.den + 1))] with n hn
    symm
    exact rowCoeff_residue_of_rational q hq n (by omega) (by omega)
  simpa using ht.congr' he

end RowRemainderBounds

#print axioms RowRemainderBounds.rowTail_sublinear


#print axioms RowRemainderBounds.rowCoeff_residue_tendsto_one_of_rational
