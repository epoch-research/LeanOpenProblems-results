import FormalConjecturesUtil

namespace Erdos371

theorem consecutive_maxPrimeFac_ne (n : ℕ) :
    Nat.maxPrimeFac (n + 1) ≠ Nat.maxPrimeFac n := by
  rcases n with _ | _ | n
  · simp
  · norm_num [Nat.prime_two.maxPrimeFac_eq_self]
  · intro h
    have hp := Nat.prime_maxPrimeFac_of_one_lt (n + 2) (by omega)
    have hd : Nat.maxPrimeFac (n + 2) ∣ (n + 2) + 1 := by
      rw [← h]
      exact Nat.maxPrimeFac_dvd
    have hone : Nat.maxPrimeFac (n + 2) ∣ 1 :=
      (Nat.dvd_add_iff_right Nat.maxPrimeFac_dvd).mpr hd
    exact hp.not_dvd_one hone

theorem comparison_complement :
    {n : ℕ | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}ᶜ =
      {n : ℕ | Nat.maxPrimeFac (n + 1) < Nat.maxPrimeFac n} := by
  ext n
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  exact ⟨fun h => lt_of_le_of_ne h (consecutive_maxPrimeFac_ne n), le_of_lt⟩


theorem comparison_count_partition (N : ℕ) :
    ((Finset.range N).filter fun n => Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n).card +
    ((Finset.range N).filter fun n => Nat.maxPrimeFac (n + 1) < Nat.maxPrimeFac n).card = N := by
  classical
  have h (n : ℕ) :
      ¬(Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n) ↔
        Nat.maxPrimeFac (n + 1) < Nat.maxPrimeFac n := by
    simp only [not_lt]
    exact ⟨fun hn => lt_of_le_of_ne hn (consecutive_maxPrimeFac_ne n), le_of_lt⟩
  simpa only [h, Finset.card_range] using
    (Finset.card_filter_add_card_filter_not
      (s := Finset.range N) (fun n => Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n))


open Filter in
theorem density_iff_count (P : ℕ → Prop) [DecidablePred P] (d : ℝ) :
    {n | P n}.HasDensity d ↔
      Tendsto (fun N : ℕ => (((Finset.range N).filter P).card : ℝ) / N)
        atTop (nhds d) := by
  have h (N : ℕ) : {n | P n} ∩ Set.Iio N =
      ((Finset.range N).filter P : Set ℕ) := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iio,
      Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact and_comm
  simp only [Set.HasDensity, Set.partialDensity, Set.inter_univ, h,
    Set.ncard_coe_finset, Set.univ_inter, Nat.ncard_Iio]

noncomputable def risingCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n).card

noncomputable def fallingCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => Nat.maxPrimeFac (n + 1) < Nat.maxPrimeFac n).card

open Filter in
theorem density_iff_signed_count :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => ((risingCount N : ℝ) - fallingCount N) / N)
        atTop (nhds 0) := by
  rw [density_iff_count]
  change Tendsto (fun N : ℕ => (risingCount N : ℝ) / N) atTop (nhds (1 / 2)) ↔ _
  have h (N : ℕ) (hN : N ≠ 0) :
      ((risingCount N : ℝ) - fallingCount N) / N =
        2 * ((risingCount N : ℝ) / N) - 1 := by
    have hc : (risingCount N : ℝ) + fallingCount N = N := by
      exact_mod_cast comparison_count_partition N
    have hz : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    field_simp
    nlinarith
  constructor
  · intro ht
    have ht' := (ht.const_mul 2).sub_const 1
    norm_num at ht'
    apply ht'.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (h N (by omega)).symm
  · intro ht
    have ht' := (ht.add_const 1).div_const 2
    norm_num at ht'
    apply ht'.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [h N (by omega)]
    ring


/-- The largest prime divisor visible through a fixed modulus. -/
def cutoffPrime (M n : ℕ) : ℕ := Nat.maxPrimeFac (Nat.gcd n M)

theorem cutoffPrime_periodic (M : ℕ) : Function.Periodic (cutoffPrime M) M := by
  intro n
  simp only [cutoffPrime, Nat.gcd_add_self_left]

theorem cutoffPrime_reflection (M n : ℕ) (hn : n ≤ M) :
    cutoffPrime M (M - n) = cutoffPrime M n := by
  simp only [cutoffPrime, Nat.gcd_self_sub_left hn]

theorem cutoffPrime_ne (M n : ℕ) (hM : 0 < M) (heven : 2 ∣ M) :
    cutoffPrime M (n + 1) ≠ cutoffPrime M n := by
  intro heq
  have hd (a : ℕ) : cutoffPrime M a ∣ a :=
    Nat.dvd_trans Nat.maxPrimeFac_dvd (Nat.gcd_dvd_left a M)
  have hone : cutoffPrime M n = 1 := by
    apply Nat.dvd_one.mp
    apply (Nat.dvd_add_iff_right (hd n)).mpr
    rw [← heq]
    exact hd (n + 1)
  have htwo (a : ℕ) (ha : 2 ∣ a) : 2 ≤ cutoffPrime M a :=
    Nat.le_maxPrimeFac (Nat.gcd_pos_of_pos_right a hM).ne' Nat.prime_two
      (Nat.dvd_gcd ha heven)
  have hpar : 2 ∣ n ∨ 2 ∣ (n + 1) := by omega
  rcases hpar with h | h
  · have := htwo n h
    omega
  · have := htwo (n + 1) h
    omega

theorem cutoff_comparison_count_eq (M : ℕ) :
    ((Finset.range M).filter fun n => cutoffPrime M (n + 1) > cutoffPrime M n).card =
    ((Finset.range M).filter fun n => cutoffPrime M (n + 1) < cutoffPrime M n).card := by
  have hswap (n : ℕ) (hn : n < M) :
      cutoffPrime M (M - 1 - n) = cutoffPrime M (n + 1) ∧
      cutoffPrime M (M - 1 - n + 1) = cutoffPrime M n := by
    constructor
    · have he : M - 1 - n = M - (n + 1) := by omega
      rw [he, cutoffPrime_reflection M (n + 1) (by omega)]
    · have he : M - 1 - n + 1 = M - n := by omega
      rw [he, cutoffPrime_reflection M n (by omega)]
  refine Finset.card_bij (fun n _ => M - 1 - n) ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    obtain ⟨h₁, h₂⟩ := hswap n hn.1
    exact ⟨by omega, by simpa only [h₁, h₂] using hn.2⟩
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    dsimp at hab
    omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    refine ⟨M - 1 - n, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      obtain ⟨h₁, h₂⟩ := hswap n hn.1
      exact ⟨by omega, by simpa only [h₁, h₂] using hn.2⟩
    · dsimp
      omega

theorem cutoff_comparison_count_half (M : ℕ) (hM : 0 < M) (heven : 2 ∣ M) :
    2 * ((Finset.range M).filter fun n =>
      cutoffPrime M (n + 1) > cutoffPrime M n).card = M := by
  have h (n : ℕ) : ¬(cutoffPrime M (n + 1) > cutoffPrime M n) ↔
      cutoffPrime M (n + 1) < cutoffPrime M n := by
    simp only [not_lt]
    exact ⟨fun h => lt_of_le_of_ne h (cutoffPrime_ne M n hM heven), le_of_lt⟩
  have hp := Finset.card_filter_add_card_filter_not (s := Finset.range M)
    (fun n => cutoffPrime M (n + 1) > cutoffPrime M n)
  simp only [h, Finset.card_range, ← cutoff_comparison_count_eq M] at hp
  omega

theorem periodic_sum_zero_bound (f : ℕ → ℝ) (M : ℕ) (hM : 0 < M)
    (hp : Function.Periodic f M) (hz : ∑ n ∈ Finset.range M, f n = 0)
    (hb : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, f n‖ ≤ M := by
  have hper (q n : ℕ) : f (q * M + n) = f n := by
    simpa only [Nat.cast_id, Nat.add_comm] using hp.nat_mul q n
  have hsum (q : ℕ) : ∑ n ∈ Finset.range (q * M), f n = 0 := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      simpa only [hper, zero_add] using hz
  have heq : ∑ n ∈ Finset.range N, f n = ∑ n ∈ Finset.range (N % M), f n := by
    conv_lhs => rw [← Nat.mod_add_div' N M, Nat.add_comm, Finset.sum_range_add]
    simp only [hsum, hper, zero_add]
  rw [heq]
  calc
    _ ≤ ∑ n ∈ Finset.range (N % M), ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range (N % M), (1 : ℝ) := Finset.sum_le_sum fun n _ => hb n
    _ = (N % M : ℕ) := by simp
    _ ≤ M := by exact_mod_cast (Nat.mod_lt N hM).le

open Filter in
theorem periodic_zero_mean_tendsto (f : ℕ → ℝ) (M : ℕ) (hM : 0 < M)
    (hp : Function.Periodic f M) (hz : ∑ n ∈ Finset.range M, f n = 0)
    (hb : ∀ n, ‖f n‖ ≤ 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f n) / N) atTop (nhds 0) := by
  apply squeeze_zero_norm (a := fun N : ℕ => (M : ℝ) / N)
  · intro N
    rw [norm_div]
    simp only [Real.norm_natCast]
    exact div_le_div_of_nonneg_right (periodic_sum_zero_bound f M hM hp hz hb N)
      (Nat.cast_nonneg N)
  · exact tendsto_const_div_atTop_nhds_zero_nat _

def predicateSign (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : ℝ :=
  if P n then 1 else -1

theorem predicateSign_sum (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    (∑ n ∈ Finset.range N, predicateSign P n) =
      2 * (((Finset.range N).filter P).card : ℝ) - N := by
  have h (n : ℕ) : predicateSign P n = 2 * (if P n then 1 else 0) - 1 := by
    unfold predicateSign
    split_ifs <;> norm_num
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

open Filter in
theorem cutoff_hasDensity_half (M : ℕ) (hM : 0 < M) (heven : 2 ∣ M) :
    {n : ℕ | cutoffPrime M (n + 1) > cutoffPrime M n}.HasDensity (1 / 2) := by
  let P := fun n => cutoffPrime M (n + 1) > cutoffPrime M n
  have hper : Function.Periodic (predicateSign P) M := by
    intro n
    have h₁ := cutoffPrime_periodic M n
    have h₂ := cutoffPrime_periodic M (n + 1)
    simp only [predicateSign, P]
    simp only [show n + M + 1 = (n + 1) + M by omega, h₁, h₂]
  have hz : ∑ n ∈ Finset.range M, predicateSign P n = 0 := by
    rw [predicateSign_sum]
    have h : 2 * (((Finset.range M).filter P).card : ℝ) = M := by
      exact_mod_cast cutoff_comparison_count_half M hM heven
    linarith
  have hb (n : ℕ) : ‖predicateSign P n‖ ≤ 1 := by
    unfold predicateSign
    split_ifs <;> norm_num
  have ht := periodic_zero_mean_tendsto (predicateSign P) M hM hper hz hb
  rw [density_iff_count]
  have ht' := (ht.add_const 1).div_const 2
  norm_num at ht'
  apply ht'.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [predicateSign_sum]
  have hzN : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  change ( (2 * (((Finset.range N).filter P).card : ℝ) - N) / N + 1) / 2 =
    (((Finset.range N).filter P).card : ℝ) / N
  field_simp
  <;> ring


open Filter in
theorem bounded_maxPrimeFac_hasDensity_zero (B : ℕ) :
    {n : ℕ | Nat.maxPrimeFac n ≤ B}.HasDensity 0 := by
  rw [density_iff_count]
  let C : ℕ := 2 ^ (B + 1).primesBelow.card
  have hcard (N : ℕ) :
      ((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B).card ≤ C * N.sqrt + 1 := by
    have hsub : ((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B) ⊆
        insert 0 (Nat.smoothNumbersUpTo N (B + 1)) := by
      intro n hn
      obtain ⟨hnN, hnB⟩ := Finset.mem_filter.mp hn
      by_cases hn : n = 0
      · simp [hn]
      · apply Finset.mem_insert_of_mem
        apply Nat.mem_smoothNumbersUpTo.mpr
        refine ⟨(Finset.mem_range.mp hnN).le, Nat.mem_smoothNumbers'.mpr ?_⟩
        intro p hp hpn
        exact Nat.lt_succ_of_le ((Nat.le_maxPrimeFac hn hp hpn).trans hnB)
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_insert_le _ _).trans
        (Nat.add_le_add_right (Nat.smoothNumbersUpTo_card_le N (B + 1)) 1))
  have hsqrt (N : ℕ) : (N.sqrt : ℝ) ≤ Real.sqrt N := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast (show N.sqrt ^ 2 ≤ N by simpa [pow_two] using Nat.sqrt_le N)
  have hbound (N : ℕ) :
      (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) / N ≤
        (C : ℝ) * (Real.sqrt N)⁻¹ + 1 / N := by
    have hc : (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) ≤
        (C : ℝ) * N.sqrt + 1 := by exact_mod_cast hcard N
    calc
      _ ≤ ((C : ℝ) * N.sqrt + 1) / N :=
        div_le_div_of_nonneg_right hc (Nat.cast_nonneg N)
      _ ≤ ((C : ℝ) * Real.sqrt N + 1) / N := by
        gcongr
        exact hsqrt N
      _ = _ := by rw [add_div, mul_div_assoc, Real.sqrt_div_self]
  have ht : Tendsto (fun N : ℕ => (C : ℝ) * (Real.sqrt N)⁻¹ + 1 / N)
      atTop (nhds 0) := by
    have hi : Tendsto (fun N : ℕ => (Real.sqrt N)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    simpa using (hi.const_mul (C : ℝ)).add tendsto_one_div_atTop_nhds_zero_nat
  exact squeeze_zero (fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N)) hbound ht


theorem cutoff_agreement_hasDensity_zero (M : ℕ) (hM : 0 < M) :
    {n : ℕ | cutoffPrime M n = Nat.maxPrimeFac n}.HasDensity 0 := by
  have hB := bounded_maxPrimeFac_hasDensity_zero M
  rw [density_iff_count] at hB ⊢
  refine squeeze_zero
    (fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N)) (fun N => ?_) hB
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnN, heq⟩ := Finset.mem_filter.mp hn
  apply Finset.mem_filter.mpr
  refine ⟨hnN, ?_⟩
  rw [← heq]
  exact Nat.maxPrimeFac_le.trans (Nat.gcd_le_right n hM)



/-- A finite-period discrepancy need not be bounded by the number of prime labels. -/
theorem cutoff_count_210_45 :
    ((Finset.range 45).filter fun n =>
      cutoffPrime 210 (n + 1) > cutoffPrime 210 n).card = 25 := by
  decide +kernel


theorem maxPrimeFac_ne_of_coprime (m n : ℕ) (hm : 1 < m) (hn : 1 < n)
    (hc : Nat.Coprime m n) : Nat.maxPrimeFac m ≠ Nat.maxPrimeFac n := by
  intro heq
  have hd : Nat.maxPrimeFac m ∣ Nat.gcd m n := Nat.dvd_gcd
    Nat.maxPrimeFac_dvd (by rw [heq]; exact Nat.maxPrimeFac_dvd)
  rw [hc.gcd_eq_one] at hd
  exact (Nat.prime_maxPrimeFac_of_one_lt m hm).not_dvd_one hd

theorem maxPrimeFac_two_mul (n : ℕ) (hn : 2 ≤ n) :
    Nat.maxPrimeFac (2 * n) = Nat.maxPrimeFac n := by
  rw [Nat.maxPrimeFac_mul (by decide) (by omega), Nat.prime_two.maxPrimeFac_eq_self]
  exact max_eq_right (Nat.prime_maxPrimeFac_of_one_lt n (by omega)).two_le

theorem signed_order_three (a b c : ℕ) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (if a < b then (1 : ℝ) else -1) + (if b < c then 1 else -1) =
      if (a < b ∧ b < c) ∨ (c < b ∧ b < a) then
        2 * (if a < c then 1 else -1) else 0 := by
  split_ifs <;> norm_num <;> omega

def factorSign (n : ℕ) : ℝ :=
  predicateSign (fun m => Nat.maxPrimeFac (m + 1) > Nat.maxPrimeFac m) n

def factorBetween (n : ℕ) : Prop :=
  (Nat.maxPrimeFac n < Nat.maxPrimeFac (2 * n + 1) ∧
    Nat.maxPrimeFac (2 * n + 1) < Nat.maxPrimeFac (n + 1)) ∨
  (Nat.maxPrimeFac (n + 1) < Nat.maxPrimeFac (2 * n + 1) ∧
    Nat.maxPrimeFac (2 * n + 1) < Nat.maxPrimeFac n)

instance (n : ℕ) : Decidable (factorBetween n) := inferInstanceAs (Decidable (_ ∨ _))

theorem factorSign_dyadic (n : ℕ) (hn : 2 ≤ n) :
    factorSign (2 * n) + factorSign (2 * n + 1) =
      if factorBetween n then 2 * factorSign n else 0 := by
  have hcop₁ : Nat.Coprime (2 * n + 1) n := by
    simpa only [Nat.add_comm] using
      (Nat.coprime_add_mul_right_left 1 n 2).mpr (by simp)
  have hcop₂ : Nat.Coprime (2 * n + 1) (n + 1) := by
    rw [← Nat.coprime_sub_self_left (show n + 1 ≤ 2 * n + 1 by omega)]
    rw [show 2 * n + 1 - (n + 1) = n by omega]
    simp
  have h₁ := maxPrimeFac_ne_of_coprime (2 * n + 1) n (by omega) (by omega) hcop₁
  have h₂ := maxPrimeFac_ne_of_coprime (2 * n + 1) (n + 1) (by omega) (by omega) hcop₂
  simp only [factorSign, predicateSign, factorBetween,
    show 2 * n + 1 + 1 = 2 * (n + 1) by omega,
    maxPrimeFac_two_mul n hn, maxPrimeFac_two_mul (n + 1) (by omega)]
  exact signed_order_three _ _ _ h₁.symm h₂ (consecutive_maxPrimeFac_ne n).symm

#print axioms consecutive_maxPrimeFac_ne
#print axioms comparison_complement
#print axioms comparison_count_partition
#print axioms density_iff_signed_count
#print axioms cutoff_comparison_count_half
#print axioms cutoff_hasDensity_half
#print axioms bounded_maxPrimeFac_hasDensity_zero
#print axioms cutoff_agreement_hasDensity_zero
#print axioms factorSign_dyadic

/-- Multiplication by a fixed positive integer changes the largest prime factor
only on a set of density zero. -/
theorem maxPrimeFac_mul_disagreement_hasDensity_zero (k : ℕ) (hk : 0 < k) :
    {n : ℕ | Nat.maxPrimeFac (k * n) ≠ Nat.maxPrimeFac n}.HasDensity 0 := by
  have hB := bounded_maxPrimeFac_hasDensity_zero k
  rw [density_iff_count] at hB ⊢
  refine squeeze_zero
    (fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N)) (fun N => ?_) hB
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnN, hne⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨hnN, ?_⟩
  by_contra h
  have hn0 : n ≠ 0 := by
    intro he
    subst n
    simp at hne
  rw [Nat.maxPrimeFac_mul hk.ne' hn0,
    max_eq_right (Nat.maxPrimeFac_le.trans (by omega))] at hne
  exact hne rfl

#print axioms maxPrimeFac_mul_disagreement_hasDensity_zero

/-- The factor remaining after removing one copy of the largest prime factor. -/
def primeCofactor (n : ℕ) : ℕ := n / Nat.maxPrimeFac n

theorem maxPrimeFac_mul_primeCofactor (n : ℕ) :
    Nat.maxPrimeFac n * primeCofactor n = n :=
  Nat.mul_div_cancel' Nat.maxPrimeFac_dvd

theorem maxPrimeFac_rise_iff_cofactor_le (n : ℕ) (hn : 0 < n) :
    Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) ↔
      primeCofactor (n + 1) ≤ primeCofactor n := by
  have he₁ := maxPrimeFac_mul_primeCofactor n
  have he₂ := maxPrimeFac_mul_primeCofactor (n + 1)
  constructor
  · intro h
    by_contra hc
    have hm := Nat.mul_le_mul (Nat.succ_le_iff.mpr h)
      (Nat.succ_le_iff.mpr (lt_of_not_ge hc))
    have hp : 0 < Nat.maxPrimeFac n := by
      by_contra hp
      have hp0 : Nat.maxPrimeFac n = 0 := by omega
      simp only [hp0, zero_mul] at he₁
      omega
    nlinarith
  · intro hc
    by_contra h
    have hm := Nat.mul_le_mul (le_of_not_gt h) hc
    omega

theorem consecutive_primeCofactor_ne (n : ℕ) (hn : 3 ≤ n) :
    primeCofactor (n + 1) ≠ primeCofactor n := by
  intro hc
  have he₁ := maxPrimeFac_mul_primeCofactor n
  have he₂ := maxPrimeFac_mul_primeCofactor (n + 1)
  have hd₁ : primeCofactor n ∣ n := ⟨Nat.maxPrimeFac n, by nlinarith⟩
  have hd₂ : primeCofactor n ∣ n + 1 := ⟨Nat.maxPrimeFac (n + 1), by
    rw [hc] at he₂
    nlinarith⟩
  have hunit : primeCofactor n = 1 := Nat.dvd_one.mp
    ((Nat.dvd_add_iff_right hd₁).mpr hd₂)
  rw [hunit, mul_one] at he₁
  rw [hc, hunit, mul_one] at he₂
  have hp₁ := Nat.prime_maxPrimeFac_of_one_lt n (by omega)
  have hp₂ := Nat.prime_maxPrimeFac_of_one_lt (n + 1) (by omega)
  rw [he₁] at hp₁
  rw [he₂] at hp₂
  have ho₁ := hp₁.eq_two_or_odd
  have ho₂ := hp₂.eq_two_or_odd
  omega

theorem maxPrimeFac_rise_iff_cofactor_fall (n : ℕ) (hn : 3 ≤ n) :
    Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) ↔
      primeCofactor (n + 1) < primeCofactor n := by
  rw [maxPrimeFac_rise_iff_cofactor_le n (by omega)]
  have hne := consecutive_primeCofactor_ne n hn
  omega

#print axioms maxPrimeFac_rise_iff_cofactor_fall

/-- A cutoff discrepancy can exceed even the number of its distinct values,
including the value `1`; a uniform bound by that number is therefore unavailable. -/
theorem cutoff_count_2310_607 :
    ((Finset.range 607).filter fun n =>
      cutoffPrime 2310 (n + 1) > cutoffPrime 2310 n).card = 300 := by
  decide +kernel

#print axioms cutoff_count_2310_607

/-- Changing a predicate on an exceptional set changes its finite count by at most
that exceptional set's finite count. -/
theorem filter_count_difference_bound (P Q D : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred D]
    (h : ∀ n, ¬ D n → (P n ↔ Q n)) (N : ℕ) :
    ‖((((Finset.range N).filter P).card : ℝ) -
        (((Finset.range N).filter Q).card : ℝ))‖ ≤
      (((Finset.range N).filter D).card : ℝ) := by
  have he : ((((Finset.range N).filter P).card : ℝ) -
      (((Finset.range N).filter Q).card : ℝ)) =
      ∑ n ∈ Finset.range N, ((if P n then (1 : ℝ) else 0) -
        (if Q n then 1 else 0)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_boole]
  rw [he]
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖((if P n then (1 : ℝ) else 0) -
        (if Q n then 1 else 0))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, (if D n then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro n _
      by_cases hd : D n
      · simp only [if_pos hd]
        split_ifs <;> norm_num
      · simp only [h n hd, sub_self, norm_zero, if_neg hd, le_refl]
    _ = _ := by simp only [Finset.sum_boole]

open Filter in
/-- Density-zero exceptions contribute a vanishing normalized count difference. -/
theorem tendsto_count_difference_of_exception (P Q D : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred D]
    (h : ∀ n, ¬ D n → (P n ↔ Q n)) (hD : {n | D n}.HasDensity 0) :
    Tendsto (fun N : ℕ =>
      ((((Finset.range N).filter P).card : ℝ) -
        (((Finset.range N).filter Q).card : ℝ)) / N) atTop (nhds 0) := by
  rw [density_iff_count] at hD
  apply squeeze_zero_norm (a := fun N : ℕ =>
    (((Finset.range N).filter D).card : ℝ) / N) _ hD
  intro N
  rw [norm_div]
  simp only [Real.norm_natCast]
  exact div_le_div_of_nonneg_right (filter_count_difference_bound P Q D h N)
    (Nat.cast_nonneg N)

theorem density_iff_of_exception (P Q D : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred D]
    (h : ∀ n, ¬ D n → (P n ↔ Q n)) (hD : {n | D n}.HasDensity 0) (d : ℝ) :
    {n | P n}.HasDensity d ↔ {n | Q n}.HasDensity d := by
  have ht := tendsto_count_difference_of_exception P Q D h hD
  simp only [sub_div] at ht
  rw [density_iff_count, density_iff_count]
  constructor
  · intro hp
    simpa only [sub_zero, sub_sub_cancel] using hp.sub ht
  · intro hq
    simpa only [add_zero, add_sub_cancel] using hq.add ht

/-- Multiplying both consecutive integers by a fixed positive integer preserves
the comparison whenever the original largest prime factor exceeds that integer. -/
theorem scaled_comparison_iff_of_large (k n : ℕ) (hk : 0 < k)
    (hn : k < Nat.maxPrimeFac n) :
    (Nat.maxPrimeFac (k * n) < Nat.maxPrimeFac (k * (n + 1))) ↔
      Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) := by
  have hn0 : n ≠ 0 := by
    intro he
    subst n
    simp only [Nat.maxPrimeFac_zero] at hn
    omega
  have hkp : Nat.maxPrimeFac k ≤ Nat.maxPrimeFac n :=
    Nat.maxPrimeFac_le.trans hn.le
  rw [Nat.maxPrimeFac_mul hk.ne' hn0,
    Nat.maxPrimeFac_mul hk.ne' (by omega), max_eq_right hkp, lt_max_iff]
  simp only [not_lt.mpr hkp, false_or]

/-- The comparison along multiples of any fixed positive integer has exactly the
same possible natural density as the original comparison. -/
theorem scaled_comparison_density_iff (k : ℕ) (hk : 0 < k) (d : ℝ) :
    {n : ℕ | Nat.maxPrimeFac (k * n) < Nat.maxPrimeFac (k * (n + 1))}.HasDensity d ↔
      {n : ℕ | Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1)}.HasDensity d := by
  apply density_iff_of_exception _ _ (fun n => Nat.maxPrimeFac n ≤ k)
  · intro n hn
    exact scaled_comparison_iff_of_large k n hk (lt_of_not_ge hn)
  · exact bounded_maxPrimeFac_hasDensity_zero k

#print axioms scaled_comparison_density_iff

/-- Equal largest prime factors at a fixed positive gap must divide that gap. -/
theorem maxPrimeFac_le_gap_of_eq (n h : ℕ) (hh : 0 < h)
    (heq : Nat.maxPrimeFac (n + h) = Nat.maxPrimeFac n) :
    Nat.maxPrimeFac n ≤ h := by
  have hd : Nat.maxPrimeFac n ∣ n + h := by
    rw [← heq]
    exact Nat.maxPrimeFac_dvd
  exact Nat.le_of_dvd hh ((Nat.dvd_add_iff_right Nat.maxPrimeFac_dvd).mpr hd)

/-- For every fixed positive gap, ties between largest prime factors have density zero. -/
theorem fixed_gap_ties_hasDensity_zero (h : ℕ) (hh : 0 < h) :
    {n : ℕ | Nat.maxPrimeFac (n + h) = Nat.maxPrimeFac n}.HasDensity 0 := by
  have he (n : ℕ) (hn : ¬ Nat.maxPrimeFac n ≤ h) :
      (Nat.maxPrimeFac (n + h) = Nat.maxPrimeFac n) ↔ False := by
    simp only [iff_false]
    exact fun ht => hn (maxPrimeFac_le_gap_of_eq n h hh ht)
  apply (density_iff_of_exception
    (fun n => Nat.maxPrimeFac (n + h) = Nat.maxPrimeFac n)
    (fun _ => False) (fun n => Nat.maxPrimeFac n ≤ h) he
    (bounded_maxPrimeFac_hasDensity_zero h) 0).mpr
  simpa only [Set.setOf_false] using (Set.HasDensity.empty (β := ℕ))

/-- The tie-free portion of any fixed-gap comparison has density one. -/
theorem fixed_gap_unequal_hasDensity_one (h : ℕ) (hh : 0 < h) :
    {n : ℕ | Nat.maxPrimeFac (n + h) ≠ Nat.maxPrimeFac n}.HasDensity 1 := by
  apply (density_iff_of_exception
    (fun n => Nat.maxPrimeFac (n + h) ≠ Nat.maxPrimeFac n)
    (fun _ => True) (fun n => Nat.maxPrimeFac (n + h) = Nat.maxPrimeFac n)
    (fun _ hn => ⟨fun _ => True.intro, fun _ => hn⟩)
    (fixed_gap_ties_hasDensity_zero h hh) 1).mpr
  simpa only [Set.setOf_true] using (Set.HasDensity.univ (β := ℕ))

#print axioms fixed_gap_unequal_hasDensity_one

/-- Only the largest prime factor of the multiplier matters in the scaling reduction. -/
theorem scaled_comparison_iff_of_maxPrimeFac_lt (k n : ℕ) (hk : 0 < k)
    (hn : Nat.maxPrimeFac k < Nat.maxPrimeFac n) :
    (Nat.maxPrimeFac (k * n) < Nat.maxPrimeFac (k * (n + 1))) ↔
      Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1) := by
  have hn0 : n ≠ 0 := by
    intro he
    subst n
    simp only [Nat.maxPrimeFac_zero] at hn
    omega
  rw [Nat.maxPrimeFac_mul hk.ne' hn0,
    Nat.maxPrimeFac_mul hk.ne' (by omega), max_eq_right hn.le, lt_max_iff]
  simp only [not_lt.mpr hn.le, false_or]

/-- Uniform finite-count control for all positive multipliers with bounded
largest prime factor, regardless of the sizes of the multipliers. -/
theorem smooth_scaling_count_difference_bound (B : ℕ) (k : ℕ → ℕ)
    (hk : ∀ n, 0 < k n) (hB : ∀ n, Nat.maxPrimeFac (k n) ≤ B) (N : ℕ) :
    ‖((((Finset.range N).filter fun n =>
        Nat.maxPrimeFac (k n * n) < Nat.maxPrimeFac (k n * (n + 1))).card : ℝ) -
      (((Finset.range N).filter fun n =>
        Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1)).card : ℝ))‖ ≤
      (((Finset.range N).filter fun n => Nat.maxPrimeFac n ≤ B).card : ℝ) := by
  apply filter_count_difference_bound
  intro n hn
  exact scaled_comparison_iff_of_maxPrimeFac_lt (k n) n (hk n)
    ((hB n).trans_lt (lt_of_not_ge hn))

/-- Arbitrarily varying positive smooth multipliers do not change the possible density. -/
theorem varying_smooth_scaling_density_iff (B : ℕ) (k : ℕ → ℕ)
    (hk : ∀ n, 0 < k n) (hB : ∀ n, Nat.maxPrimeFac (k n) ≤ B) (d : ℝ) :
    {n : ℕ | Nat.maxPrimeFac (k n * n) < Nat.maxPrimeFac (k n * (n + 1))}.HasDensity d ↔
      {n : ℕ | Nat.maxPrimeFac n < Nat.maxPrimeFac (n + 1)}.HasDensity d := by
  apply density_iff_of_exception _ _ (fun n => Nat.maxPrimeFac n ≤ B)
  · intro n hn
    exact scaled_comparison_iff_of_maxPrimeFac_lt (k n) n (hk n)
      ((hB n).trans_lt (lt_of_not_ge hn))
  · exact bounded_maxPrimeFac_hasDensity_zero B

#print axioms varying_smooth_scaling_density_iff

end Erdos371
