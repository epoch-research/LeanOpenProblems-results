import Submission.RowRemainderBounds

/-!
Sharper quantitative bounds on the rowwise factorial remainder.
These estimates do not settle Erdős 68.
-/

namespace SharperRowRemainderBounds

open Erdos68Development RowRemainderBounds

lemma factorial_block_bound (C k : ℕ) :
    (C * k).factorial ≤ C ^ (C * k) * k.factorial ^ C := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      (C * (k + 1)).factorial =
          (C * k).factorial * (C * k + 1).ascFactorial C := by
        rw [Nat.factorial_mul_ascFactorial]
        congr 1
      _ ≤ (C ^ (C * k) * k.factorial ^ C) * (C * k + C) ^ C :=
        Nat.mul_le_mul ih (Nat.ascFactorial_le_pow_add (C * k) C)
      _ = C ^ (C * (k + 1)) * (k + 1).factorial ^ C := by
        rw [show C * k + C = C * (k + 1) by ring, mul_pow,
          Nat.factorial_succ, mul_pow, show C * (k + 1) = C * k + C by ring,
          pow_add]
        ring

lemma factorial_power_large_sharp (n k C J L : ℕ)
    (hJ : 0 < J) (hL : 0 < L) (hC : C ≤ J) (hCk : C * k ≤ 2 * n)
    (hn : (2 * J ^ 2) ^ L ≤ n)
    (hgap : n / L < C * k - n) :
    n.factorial * 2 ^ n ≤ k.factorial ^ C := by
  have hslack : n < L * (C * k - n) := by
    simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hL).mp hgap
  have hkn : n ≤ C * k := by
    have : 0 < C * k - n := lt_of_le_of_lt (Nat.zero_le _) hgap
    omega
  have hlo := @Nat.factorial_mul_pow_le_factorial n (C * k - n)
  rw [Nat.add_sub_of_le hkn] at hlo
  have hu := factorial_block_bound C k
  have hbase : C ^ (C * k) * 2 ^ n ≤ (2 * J ^ 2) ^ n := by
    calc
      C ^ (C * k) * 2 ^ n ≤ J ^ (2 * n) * 2 ^ n := by
        apply Nat.mul_le_mul_right
        exact (Nat.pow_le_pow_left hC _).trans
          (Nat.pow_le_pow_right hJ hCk)
      _ = (2 * J ^ 2) ^ n := by rw [pow_mul, mul_pow]; ring
  have hp : C ^ (C * k) * 2 ^ n ≤ (n + 1) ^ (C * k - n) := by
    calc
      C ^ (C * k) * 2 ^ n ≤ (2 * J ^ 2) ^ n := hbase
      _ ≤ (2 * J ^ 2) ^ (L * (C * k - n)) :=
        Nat.pow_le_pow_right (by positivity) hslack.le
      _ = ((2 * J ^ 2) ^ L) ^ (C * k - n) := pow_mul _ _ _
      _ ≤ (n + 1) ^ (C * k - n) := Nat.pow_le_pow_left (by omega) _
  have h := (Nat.mul_le_mul_left n.factorial hp).trans (hlo.trans hu)
  have hh : C ^ (C * k) * (n.factorial * 2 ^ n) ≤
      C ^ (C * k) * k.factorial ^ C := by nlinarith [h]
  have hCp : 0 < C := by
    by_contra hz
    have : C = 0 := by omega
    simp [this] at hgap
  exact Nat.le_of_mul_le_mul_left hh (by positivity)

lemma row_fraction_small_sharp (n k J L : ℕ)
    (hJpos : 0 < J) (hL : 0 < L) (hk2 : 2 ≤ k) (hkn : k ≤ n) (hJ : n / J < k)
    (hn : (2 * J ^ 2) ^ L ≤ n)
    (hgap : n / L < (n / k + 1) * k - n) :
    rowRemainder n k ≤ 2 / (2 : ℝ) ^ n := by
  have hC : n / k + 1 ≤ J := by
    have h1 := (Nat.div_lt_iff_lt_mul hJpos).mp hJ
    have h2 : n / k < J := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by nlinarith)
    omega
  have hCk : (n / k + 1) * k ≤ 2 * n := by
    have := Nat.div_mul_le_self n k
    nlinarith
  have hpow := factorial_power_large_sharp n k (n / k + 1) J L
    hJpos hL hC hCk hn hgap
  have hpowR : (n.factorial : ℝ) * (2 : ℝ) ^ n ≤
      (k.factorial : ℝ) ^ (n / k + 1) := by exact_mod_cast hpow
  have htwo : (2 : ℝ) ≤ k.factorial := by
    exact_mod_cast (show 2 ≤ k.factorial by simpa using Nat.factorial_le hk2)
  have hf : (0 : ℝ) < k.factorial := by positivity
  have hd : (0 : ℝ) < k.factorial - 1 := by linarith
  have hbase := row_fraction_le_geometric_tail n k (n / k) hk2 (Nat.div_mul_le_self n k)
  change (n.factorial : ℝ) / (k.factorial - 1 : ℝ) -
    ⌊(n.factorial : ℝ) / (k.factorial - 1 : ℝ)⌋ ≤ _
  refine hbase.trans ?_
  apply (div_le_div_iff₀ (mul_pos (pow_pos hf _) hd) (by positivity)).mpr
  have hh : (k.factorial : ℝ) ≤ 2 * (k.factorial - 1) := by linarith
  have hm := mul_le_mul_of_nonneg_left hh (pow_nonneg hf.le (n / k))
  rw [pow_succ] at hpowR
  nlinarith

lemma transitionBand_card_sharp_nat (n J L : ℕ) (hJ : 0 < J) :
    (transitionBand n J L).card ≤
      ∑ C ∈ Finset.Icc 1 J, ((n / L) / C + 1) := by
  let intervals : ℕ → Finset ℕ := fun C => Finset.Ioc (n / C) ((n + n / L) / C)
  have hsub : transitionBand n J L ⊆ (Finset.Icc 1 J).biUnion intervals := by
    intro k hk
    simp only [transitionBand, Finset.mem_filter, Finset.mem_Ico] at hk
    let C := n / k + 1
    have hC0 : 0 < C := Nat.succ_pos _
    have hCJ : C ≤ J := by
      have h1 := (Nat.div_lt_iff_lt_mul hJ).mp hk.2.1
      have h2 : n / k < J := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by nlinarith)
      dsimp [C]
      omega
    apply Finset.mem_biUnion.mpr
    refine ⟨C, Finset.mem_Icc.mpr ⟨hC0, hCJ⟩, ?_⟩
    change k ∈ Finset.Ioc (n / C) ((n + n / L) / C)
    have hnC : n < C * k := by
      dsimp [C]
      exact (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).mp (Nat.lt_succ_self (n / k))
    have hgap : C * k - n ≤ n / L := hk.2.2
    apply Finset.mem_Ioc.mpr
    constructor
    · exact (Nat.div_lt_iff_lt_mul hC0).mpr (by nlinarith)
    · apply (Nat.le_div_iff_mul_le hC0).mpr
      nlinarith [Nat.sub_add_cancel hnC.le]
  calc
    (transitionBand n J L).card ≤ ((Finset.Icc 1 J).biUnion intervals).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ C ∈ Finset.Icc 1 J, (intervals C).card := Finset.card_biUnion_le
    _ ≤ ∑ C ∈ Finset.Icc 1 J, ((n / L) / C + 1) := by
      apply Finset.sum_le_sum
      intro C hC
      have hCp : 0 < C := (Finset.mem_Icc.mp hC).1
      have hd := @Nat.add_div n (n / L) C hCp
      simp only [intervals, Nat.card_Ioc]
      have hz := Nat.zero_le (n / L / C)
      split_ifs at hd <;> omega

lemma transitionBand_card_sharp (n J L : ℕ) (hJ : 0 < J) :
    ((transitionBand n J L).card : ℝ) ≤
      (n / L : ℕ) * (1 + Real.log J) + J := by
  have h := transitionBand_card_sharp_nat n J L hJ
  have hR : ((transitionBand n J L).card : ℝ) ≤
      ∑ C ∈ Finset.Icc 1 J, (((n / L : ℕ) / C + 1 : ℕ) : ℝ) := by exact_mod_cast h
  calc
    ((transitionBand n J L).card : ℝ) ≤
        ∑ C ∈ Finset.Icc 1 J, (((n / L : ℕ) / C + 1 : ℕ) : ℝ) := hR
    _ ≤ ∑ C ∈ Finset.Icc 1 J, (((n / L : ℕ) : ℝ) / C + 1) := by
      apply Finset.sum_le_sum
      intro C hC
      push_cast
      exact add_le_add_left (Nat.cast_div_le (α := ℝ) (m := n / L) (n := C)) 1
    _ = (n / L : ℕ) * (harmonic J : ℝ) + J := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
        Nat.card_Icc, Nat.add_sub_cancel, harmonic_eq_sum_Icc, Rat.cast_sum,
        Rat.cast_inv, Rat.cast_natCast, Finset.mul_sum, div_eq_mul_inv]
    _ ≤ (n / L : ℕ) * (1 + Real.log J) + J := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log J)
          (Nat.cast_nonneg (α := ℝ) (n / L))) _

lemma rowRemainder_sum_bound_sharp (n J L : ℕ) (hJ : 0 < J) (hL : 0 < L)
    (hn : (2 * J ^ 2) ^ L ≤ n) :
    (∑ k ∈ Finset.Ico 2 (n + 1), rowRemainder n k) ≤
      (n / J + 1 : ℕ) + (n / L : ℕ) * (1 + Real.log J) + J +
        (n + 1 : ℝ) * (2 / (2 : ℝ) ^ n) := by
  let low := (Finset.Ico 2 (n + 1)).filter (fun k => k ≤ n / J)
  have hlcard : low.card ≤ n / J + 1 := by
    calc
      low.card ≤ (Finset.range (n / J + 1)).card := Finset.card_le_card (by
        intro k hk
        simp only [low, Finset.mem_filter, Finset.mem_Ico] at hk
        simpa only [Finset.mem_range] using (show k < n / J + 1 by omega))
      _ = _ := Finset.card_range _
  have hbcard := transitionBand_card_sharp n J L hJ
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
        exact row_fraction_small_sharp n k J L hJ hL hk'.1 (by omega) (by omega) hn (by omega)
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
  have h1 := hbcard
  have h2 : ((Finset.Ico 2 (n + 1)).card : ℝ) ≤ n + 1 := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 2 / 2 ^ n)
  linarith

lemma rowTail_bound_sharp (n J L : ℕ) (hn2 : 2 ≤ n) (hJ : 0 < J) (hL : 0 < L)
    (hn : (2 * J ^ 2) ^ L ≤ n) :
    rowTail n ≤ (n / J + 1 : ℕ) + (n / L : ℕ) * (1 + Real.log J) + J +
      (n + 1 : ℝ) * (2 / (2 : ℝ) ^ n) + 3 / (n + 1) := by
  have he := (scaled_partial_sum_error (n - 1)).2
  rw [show n - 1 + 1 = n by omega] at he
  have he' : ((n - 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  rw [he'] at he
  have hs := rowRemainder_sum_bound_sharp n J L hJ hL hn
  rw [rowRemainder_sum n hn2] at hs
  unfold rowTail
  nlinarith

/-- A quantitative bound using both the sharper factorial-block estimate and
harmonic counting of the exceptional bands. This supplies no nonintegrality
or coefficient congruence. -/
theorem rowTail_normalized_bound_sharp (n J L : ℕ) (hn2 : 2 ≤ n)
    (hJ : 0 < J) (hL : 0 < L) (hn : (2 * J ^ 2) ^ L ≤ n) :
    rowTail n / (n + 1 : ℝ) ≤ 1 / (J : ℝ) + (1 + Real.log J) / L +
      (J + 1 : ℝ) / (n + 1) + 2 / (2 : ℝ) ^ n + 3 / (n + 1 : ℝ) ^ 2 := by
  have hb := rowTail_bound_sharp n J L hn2 hJ hL hn
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hlog : 0 ≤ 1 + Real.log J := by
    have : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have := Real.log_nonneg this
    linarith
  have h0 : ((n / J : ℕ) : ℝ) ≤ (n + 1 : ℝ) / J := by
    exact Nat.cast_div_le.trans (div_le_div_of_nonneg_right (by linarith) hJr.le)
  have h1 : ((n / L : ℕ) : ℝ) ≤ (n + 1 : ℝ) / L := by
    exact Nat.cast_div_le.trans (div_le_div_of_nonneg_right (by linarith) hLr.le)
  have hm := mul_le_mul_of_nonneg_right h1 hlog
  push_cast at hb
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
  have he : (1 / (J : ℝ) + (1 + Real.log J) / L +
      (J + 1 : ℝ) / (n + 1) + 2 / (2 : ℝ) ^ n + 3 / (n + 1 : ℝ) ^ 2) *
      (n + 1 : ℝ) =
      (n + 1 : ℝ) / J + 1 + ((n + 1 : ℝ) / L) * (1 + Real.log J) + J +
      (n + 1 : ℝ) * (2 / (2 : ℝ) ^ n) + 3 / (n + 1) := by
    field_simp
    ring
  rw [he]
  nlinarith

lemma rowTail_dyadic_bound (n s : ℕ)
    (hn : 2 ^ ((2 * s + 1) * 2 ^ s) ≤ n) :
    rowTail n / (n + 1 : ℝ) ≤ (s + 2 : ℝ) / (2 : ℝ) ^ s +
      ((2 : ℝ) ^ s + 1) / (n + 1) + 2 / (2 : ℝ) ^ n + 3 / (n + 1 : ℝ) ^ 2 := by
  have hbase : (2 * (2 ^ s) ^ 2 : ℕ) = 2 ^ (2 * s + 1) := by
    calc
      2 * (2 ^ s) ^ 2 = (2 ^ s) ^ 2 * 2 := Nat.mul_comm _ _
      _ = 2 ^ (s * 2) * 2 := by rw [pow_mul]
      _ = 2 ^ (s * 2 + 1) := (pow_succ (2 : ℕ) (s * 2)).symm
      _ = 2 ^ (2 * s + 1) := by rw [Nat.mul_comm s 2]
  have hth : (2 * (2 ^ s) ^ 2 : ℕ) ^ (2 ^ s) ≤ n := by
    rw [hbase, ← pow_mul]
    exact hn
  have hexp : 1 ≤ (2 * s + 1) * 2 ^ s := by
    have hp : 0 < (2 * s + 1) * 2 ^ s := by positivity
    omega
  have hn2 : 2 ≤ n := by
    exact (show 2 ≤ 2 ^ ((2 * s + 1) * 2 ^ s) by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hexp).trans hn
  have h := rowTail_normalized_bound_sharp n (2 ^ s) (2 ^ s) hn2
    (by positivity) (by positivity) hth
  have hlog : Real.log ((2 : ℝ) ^ s) ≤ s := by
    rw [Real.log_pow]
    have h2 : Real.log 2 ≤ (1 : ℝ) := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) s]
  push_cast at h
  have he : 1 / (2 : ℝ) ^ s + (1 + Real.log ((2 : ℝ) ^ s)) / (2 : ℝ) ^ s ≤
      (s + 2 : ℝ) / (2 : ℝ) ^ s := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  linarith

/-- An explicit threshold for the improved row-tail estimate. The numerator
may still grow with n, so this does not exclude integral tails. -/
theorem rowTail_explicit_bound (n s : ℕ)
    (hn : 2 ^ ((2 * s + 1) * 2 ^ s) ≤ n) :
    rowTail n / (n + 1 : ℝ) ≤ (s + 5 : ℝ) / (2 : ℝ) ^ s := by
  have hJ : 1 ≤ (2 : ℕ) ^ s := Nat.one_le_pow _ _ (by norm_num)
  have hbaseN : 2 * (2 ^ s) ^ 2 ≤ n := by
    have hmono : 2 ^ (2 * s + 1) ≤ 2 ^ ((2 * s + 1) * 2 ^ s) := by
      apply Nat.pow_le_pow_right (by norm_num)
      nlinarith [hJ]
    have he : (2 * (2 ^ s) ^ 2 : ℕ) = 2 ^ (2 * s + 1) := by
      calc
        2 * (2 ^ s) ^ 2 = (2 ^ s) ^ 2 * 2 := Nat.mul_comm _ _
        _ = 2 ^ (s * 2) * 2 := by rw [pow_mul]
        _ = 2 ^ (s * 2 + 1) := (pow_succ (2 : ℕ) (s * 2)).symm
        _ = 2 ^ (2 * s + 1) := by rw [Nat.mul_comm s 2]
    rw [he]
    exact hmono.trans hn
  have hJr : (1 : ℝ) ≤ (2 : ℝ) ^ s := by exact_mod_cast hJ
  have hbaseR : 2 * ((2 : ℝ) ^ s) ^ 2 ≤ n := by exact_mod_cast hbaseN
  have hnJ : 2 * (2 : ℝ) ^ s ≤ n := by nlinarith
  have h1 : ((2 : ℝ) ^ s + 1) / (n + 1) ≤ 1 / (2 : ℝ) ^ s := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hsn : s + 1 ≤ n := by
    have hs : s < (2 : ℕ) ^ s := Nat.lt_two_pow_self
    nlinarith
  have hpowN : (2 : ℕ) ^ (s + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hsn
  have hpowR : (2 : ℝ) ^ s * 2 ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (show (2 : ℕ) ^ s * 2 ≤ 2 ^ n by simpa [pow_succ] using hpowN)
  have h2 : 2 / (2 : ℝ) ^ n ≤ 1 / (2 : ℝ) ^ s := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have h3 : 3 / (n + 1 : ℝ) ^ 2 ≤ 1 / (2 : ℝ) ^ s := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (n : ℝ)]
  have h := rowTail_dyadic_bound n s hn
  have he : (s + 2 : ℝ) / (2 : ℝ) ^ s + 1 / (2 : ℝ) ^ s +
      1 / (2 : ℝ) ^ s + 1 / (2 : ℝ) ^ s = (s + 5 : ℝ) / (2 : ℝ) ^ s := by ring
  linarith

/-- Rationality forces the normalized row-coefficient residue into an explicit
interval just below 1. Excluding that interval infinitely often remains open
in this development. -/
theorem rowCoeff_residue_bounds_of_rational (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) (n s : ℕ)
    (hn3 : 3 ≤ n) (hnq : q.den < n)
    (hn : 2 ^ ((2 * s + 1) * 2 ^ s) ≤ n) :
    1 - 2 * ((s + 5 : ℝ) / (2 : ℝ) ^ s) ≤
        ((rowCoeff n % (n : ℤ) : ℤ) : ℝ) / n ∧
      ((rowCoeff n % (n : ℤ) : ℤ) : ℝ) / n < 1 := by
  rw [rowCoeff_residue_of_rational q hq n hn3 hnq]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnp : (0 : ℝ) < n := by linarith
  have ht := rowTail_explicit_bound n s hn
  have hp := rowTail_pos n
  have hratio : rowTail n / (n : ℝ) ≤ 2 * (rowTail n / (n + 1 : ℝ)) := by
    apply (div_le_iff₀ hnp).mpr
    have he : 2 * (rowTail n / (n + 1 : ℝ)) * n =
        (2 * rowTail n * n) / (n + 1) := by ring
    rw [he]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
    nlinarith
  constructor
  · linarith
  · have := div_pos hp hnp
    linarith

end SharperRowRemainderBounds

#print axioms SharperRowRemainderBounds.rowTail_normalized_bound_sharp
#print axioms SharperRowRemainderBounds.rowTail_dyadic_bound
#print axioms SharperRowRemainderBounds.rowTail_explicit_bound

#print axioms SharperRowRemainderBounds.rowCoeff_residue_bounds_of_rational
