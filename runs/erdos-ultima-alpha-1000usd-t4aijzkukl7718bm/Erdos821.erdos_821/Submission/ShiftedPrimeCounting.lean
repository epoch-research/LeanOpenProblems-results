import Submission.PrimeModulusSupply

/-!
# From progression weight to shifted primes

When the moduli are prime and their minimum cube exceeds the input bound,
an integer other than 1 lies in at most two residue-one classes. This turns
the weighted progression lower bound into a lower bound for distinct primes.
-/

open scoped BigOperators
open Finset ArithmeticFunction Filter

namespace Erdos821.AnalyticSieve

lemma residue_one_iff_dvd_pred {n q : ℕ} (hn : 1 ≤ n) :
    (n : ZMod q) = 1 ↔ q ∣ n - 1 := by
  rw [← ZMod.natCast_eq_zero_iff (n - 1) q, Nat.cast_sub hn, Nat.cast_one, sub_eq_zero]

lemma prime_divisor_card_le_two (P : Finset ℕ) (D N n : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ D ≤ p ∧ p ∣ n)
    (hn : 0 < n) (hnN : n ≤ N) (hcube : N < D ^ 3) : P.card ≤ 2 := by
  have hD : 0 < D := by
    by_contra h
    have hz : D = 0 := by omega
    subst D
    norm_num at hcube
  have hprod : (∏ p ∈ P, p) ∣ n := (Erdos821.Sieve.prod_primes_dvd_iff P
    (fun p hp => (hP p hp).1) n).mpr (fun p hp => (hP p hp).2.2)
  have hprodle := Nat.le_of_dvd hn hprod
  have hlow : D ^ P.card ≤ ∏ p ∈ P, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun p hp => (hP p hp).2.1)
  by_contra hcard
  have hpow := Nat.pow_le_pow_right hD (show 3 ≤ P.card by omega)
  omega

noncomputable def modulusIncidence (M : Finset ℕ+) (n : ℕ) : ℕ :=
  (M.filter (fun q : ℕ+ => (n : ZMod (q : ℕ)) = 1)).card

lemma modulusIncidence_le_two (M : Finset ℕ+) (D N n : ℕ)
    (hM : ∀ q ∈ M, (q : ℕ).Prime ∧ D ≤ (q : ℕ))
    (hn : 2 ≤ n) (hnN : n ≤ N) (hcube : N < D ^ 3) : modulusIncidence M n ≤ 2 := by
  classical
  let S := M.filter (fun q : ℕ+ => (n : ZMod (q : ℕ)) = 1)
  have hcard : (S.image (fun q : ℕ+ => (q : ℕ))).card = S.card :=
    Finset.card_image_iff.mpr (fun a ha b hb h => PNat.coe_injective h)
  change S.card ≤ 2
  rw [← hcard]
  apply prime_divisor_card_le_two _ D N (n - 1) _ (by omega) (by omega) hcube
  intro p hp
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
  obtain ⟨hqM, hqn⟩ := mem_filter.mp hq
  exact ⟨(hM q hqM).1, (hM q hqM).2, (residue_one_iff_dvd_pred (by omega : 1 ≤ n)).mp hqn⟩

lemma sum_progressions_eq_incidence (M : Finset ℕ+) (N : ℕ) :
    (∑ q ∈ M, residueOneMangoldt q N) =
      ∑ n ∈ Icc 1 N, (modulusIncidence M n : ℝ) * vonMangoldt n := by
  classical
  simp only [residueOneMangoldt]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

lemma mangoldt_nonprime_sum_le (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Prime), vonMangoldt n) ≤
      2 * Real.sqrt N * Real.log N := by
  have h := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by exact_mod_cast hN : (1 : ℝ) ≤ N)
  have heq : (Ioc 0 N : Finset ℕ) = Icc 1 N := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  have hs := Chebyshev.psi_sub_theta_eq_sum_not_prime (N : ℝ)
  rw [Nat.floor_natCast, heq] at hs
  exact (le_abs_self _).trans (hs ▸ h)

def shiftedWitnessPrimes (M : Finset ℕ+) (B N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun p => p.Prime ∧ B < p ∧ ∃ q ∈ M, (p : ZMod (q : ℕ)) = 1)

lemma progression_weight_le_prime_count (M : Finset ℕ+) (D B N : ℕ)
    (hM : ∀ q ∈ M, (q : ℕ).Prime ∧ D ≤ (q : ℕ))
    (hN : 1 ≤ N) (hcube : N < D ^ 3) :
    (∑ q ∈ M, residueOneMangoldt q N) ≤
      2 * Real.log N * ((shiftedWitnessPrimes M B N).card + (B : ℝ) + 2 * Real.sqrt N) := by
  classical
  let G := shiftedWitnessPrimes M B N
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      (modulusIncidence M n : ℝ) * vonMangoldt n ≤
        (if n ∈ G then 2 * Real.log N else 0) +
        (if n ≤ B then 2 * Real.log N else 0) +
        (if ¬n.Prime then 2 * vonMangoldt n else 0) := by
    have hn1 := (mem_Icc.mp hn).1
    have hnN := (mem_Icc.mp hn).2
    have hlog := Real.log_natCast_nonneg N
    have hΛ := vonMangoldt_nonneg (n := n)
    by_cases hn' : n = 1
    · subst n
      simp only [vonMangoldt_apply_one, mul_zero]
      positivity
    have hinc : (modulusIncidence M n : ℝ) ≤ 2 := by
      exact_mod_cast modulusIncidence_le_two M D N n hM (by omega) hnN hcube
    have hweight := mul_le_mul_of_nonneg_right hinc hΛ
    have hweight' : (modulusIncidence M n : ℝ) * vonMangoldt n ≤ 2 * Real.log N :=
      hweight.trans (mul_le_mul_of_nonneg_left (vonMangoldt_le_log.trans (log_nat_mono hnN)) (by norm_num))
    by_cases hp : n.Prime
    · rw [if_neg (not_not.mpr hp)]
      by_cases hnB : n ≤ B
      · rw [if_pos hnB]
        split_ifs <;> linarith
      · rw [if_neg hnB]
        by_cases he : ∃ q ∈ M, (n : ZMod (q : ℕ)) = 1
        · have hnG : n ∈ G := mem_filter.mpr ⟨hn, hp, by omega, he⟩
          rw [if_pos hnG]
          linarith
        · have hzero : modulusIncidence M n = 0 := by
            unfold modulusIncidence
            rw [Finset.card_eq_zero]
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro q hq
            exact he ⟨q, (mem_filter.mp hq).1, (mem_filter.mp hq).2⟩
          simp only [hzero, Nat.cast_zero, zero_mul]
          split_ifs <;> linarith
    · rw [if_pos hp]
      split_ifs <;> linarith
  have hsmall : ((Icc 1 N).filter (fun n => n ≤ B)).card ≤ B := by
    calc
      _ ≤ (Icc 1 B).card := Finset.card_le_card (by
        intro n hn
        exact mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hn).1).1, (mem_filter.mp hn).2⟩)
      _ = B := by simp
  have hG' : (Icc 1 N).filter (fun n => n ∈ G) = G := by
    ext n
    simp only [mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨(mem_filter.mp h).1, h⟩⟩
  calc
    _ = ∑ n ∈ Icc 1 N, (modulusIncidence M n : ℝ) * vonMangoldt n := sum_progressions_eq_incidence M N
    _ ≤ ∑ n ∈ Icc 1 N, ((if n ∈ G then 2 * Real.log N else 0) +
        (if n ≤ B then 2 * Real.log N else 0) + (if ¬n.Prime then 2 * vonMangoldt n else 0)) :=
      Finset.sum_le_sum hpoint
    _ = (G.card : ℝ) * (2 * Real.log N) +
        (((Icc 1 N).filter (fun n => n ≤ B)).card : ℝ) * (2 * Real.log N) +
        2 * (∑ n ∈ (Icc 1 N).filter (fun n => ¬n.Prime), vonMangoldt n) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [← Finset.sum_filter, hG', Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    _ ≤ (G.card : ℝ) * (2 * Real.log N) + (B : ℝ) * (2 * Real.log N) +
        2 * (2 * Real.sqrt N * Real.log N) := by
      apply add_le_add
      · exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast hsmall)
          (by have := Real.log_natCast_nonneg N; positivity))
      · exact mul_le_mul_of_nonneg_left (mangoldt_nonprime_sum_le N hN) (by norm_num)
    _ = _ := by dsimp [G]; ring

def progressionScaleB (s L : ℕ) : ℕ := 2 ^ (64 * s - L)

lemma progression_scale_cube {s L : ℕ} (hL : 1 ≤ L) (hLs : L ≤ s) :
    progressionScaleN s < (progressionScaleD s L) ^ 3 := by
  unfold progressionScaleN progressionScaleD
  rw [← pow_mul]
  apply Nat.pow_lt_pow_right (by norm_num)
  omega

lemma progressionScaleB_mul {s L : ℕ} (hLs : L ≤ s) :
    progressionScaleB s L * 2 ^ L = progressionScaleN s := by
  unfold progressionScaleB progressionScaleN
  rw [← pow_add]
  congr 1
  omega

/-- A lower bound for the number of distinct primes with a prime-modulus
witness. The bound excludes all p<=2^(64s-L). -/
theorem progression_scale_prime_count {s L : ℕ} (hL : 1 ≤ L) (hLs : L ≤ s)
    (hsmall : 32768000000000000 * (s + 1) ^ 7 ≤ 2 ^ L) :
    progressionScaleN s ≤ 8388608 * s ^ 3 *
      (shiftedWitnessPrimes
        (primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L))
        (progressionScaleB s L) (progressionScaleN s)).card := by
  let M := primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L)
  let G := shiftedWitnessPrimes M (progressionScaleB s L) (progressionScaleN s)
  have hs : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hn1 : 1 ≤ progressionScaleN s := by unfold progressionScaleN; exact one_le_pow₀ (by norm_num)
  have hlower := progression_scale_weight_lower hL hLs hsmall
  have hupper := progression_weight_le_prime_count M (progressionScaleD s L) (progressionScaleB s L)
    (progressionScaleN s) (fun q hq => ⟨(mem_primeModuliBetween.mp hq).1, (mem_primeModuliBetween.mp hq).2.1⟩)
    hn1 (progression_scale_cube hL hLs)
  have hsqrt : Real.sqrt (progressionScaleN s) ≤ (progressionScaleB s L : ℝ) := by
    rw [sqrt_progressionScaleN]
    simp only [progressionScaleB, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hlog : Real.log (progressionScaleN s) ≤ 64 * (s : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using log_two_pow_le (64 * s)
  have hup : (∑ q ∈ M, residueOneMangoldt q (progressionScaleN s)) ≤
      128 * (s : ℝ) * (G.card : ℝ) + 384 * (s : ℝ) * (progressionScaleB s L : ℝ) := by
    apply hupper.trans
    have hg0 : (0 : ℝ) ≤ G.card := Nat.cast_nonneg _
    have hb0 : (0 : ℝ) ≤ progressionScaleB s L := Nat.cast_nonneg _
    calc
      _ ≤ 2 * (64 * (s : ℝ)) * ((G.card : ℝ) + (progressionScaleB s L : ℝ) + 2 * (progressionScaleB s L : ℝ)) := by
        gcongr
      _ = _ := by ring
  have hpoly : 25165824 * s ^ 3 ≤ 2 ^ L := by
    have hp : s ^ 3 ≤ (s + 1) ^ 7 :=
      (Nat.pow_le_pow_left (Nat.le_succ s) 3).trans
        (Nat.pow_le_pow_right (show 0 < s + 1 by omega) (by norm_num : 3 ≤ 7))
    omega
  have hsmallpart : 384 * (s : ℝ) * (progressionScaleB s L : ℝ) ≤
      (progressionScaleN s : ℝ) / (65536 * (s : ℝ) ^ 2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hp : 25165824 * (s : ℝ) ^ 3 ≤ (2 : ℝ) ^ L := by exact_mod_cast hpoly
    have h := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) (progressionScaleB s L))
    have heq : (2 : ℝ) ^ L * (progressionScaleB s L : ℝ) = (progressionScaleN s : ℝ) := by
      exact_mod_cast (by rw [mul_comm]; exact progressionScaleB_mul hLs)
    rw [heq] at h
    convert h using 1; ring
  have heq : (progressionScaleN s : ℝ) / (32768 * (s : ℝ) ^ 2) =
      2 * ((progressionScaleN s : ℝ) / (65536 * (s : ℝ) ^ 2)) := by field_simp; ring
  rw [heq] at hlower
  have hg : (progressionScaleN s : ℝ) / (65536 * (s : ℝ) ^ 2) ≤ 128 * (s : ℝ) * (G.card : ℝ) := by
    linarith
  have hgc := (div_le_iff₀ (by positivity : 0 < 65536 * (s : ℝ) ^ 2)).mp hg
  have hfinal : (progressionScaleN s : ℝ) ≤ 8388608 * (s : ℝ) ^ 3 * (G.card : ℝ) := by nlinarith
  exact_mod_cast hfinal

lemma shiftedWitnessPrimes_factor_bound (M : Finset ℕ+) (D Q B N : ℕ)
    (hD : 0 < D) (hQN : Q ≤ N / D)
    (hM : ∀ q ∈ M, (q : ℕ).Prime ∧ D ≤ (q : ℕ) ∧ (q : ℕ) ≤ Q)
    {p : ℕ} (hp : p ∈ shiftedWitnessPrimes M B N) :
    p.Prime ∧ B < p ∧ p ≤ N ∧ ∀ ℓ ∈ (p - 1).primeFactorsList, ℓ ≤ N / D := by
  obtain ⟨hpI, hprime, hBp, q, hqM, hqres⟩ := mem_filter.mp hp
  have hpN := (mem_Icc.mp hpI).2
  have hnpos : 0 < p - 1 := Nat.sub_pos_of_lt hprime.one_lt
  have hqdvd : (q : ℕ) ∣ p - 1 := (residue_one_iff_dvd_pred hprime.pos).mp hqres
  have hqdata := hM q hqM
  have hquot : (p - 1) / (q : ℕ) ≤ N / D := by
    apply (Nat.le_div_iff_mul_le hD).mpr
    calc
      _ ≤ ((p - 1) / (q : ℕ)) * (q : ℕ) := Nat.mul_le_mul_left _ hqdata.2.1
      _ = p - 1 := Nat.div_mul_cancel hqdvd
      _ ≤ N := by omega
  have hquotpos : 0 < (p - 1) / (q : ℕ) := Nat.div_pos (Nat.le_of_dvd hnpos hqdvd) q.pos
  refine ⟨hprime, hBp, hpN, ?_⟩
  intro ℓ hℓ
  have hℓprime := Nat.prime_of_mem_primeFactorsList hℓ
  have hℓdvd := Nat.dvd_of_mem_primeFactorsList hℓ
  have hmul : ℓ ∣ (q : ℕ) * ((p - 1) / (q : ℕ)) := by rw [Nat.mul_div_cancel' hqdvd]; exact hℓdvd
  rcases hℓprime.dvd_mul.mp hmul with h | h
  · have heq : ℓ = (q : ℕ) := (Nat.dvd_prime hqdata.1).mp h |>.resolve_left hℓprime.ne_one
    exact heq ▸ hqdata.2.2.trans hQN
  · exact (Nat.le_of_dvd hquotpos h).trans hquot

lemma progression_scale_cofactor {s L : ℕ} (hLs : L ≤ s) :
    progressionScaleN s / progressionScaleD s L = 2 ^ (32 * s + 3 * L) := by
  unfold progressionScaleN progressionScaleD
  rw [Nat.pow_div (by omega) (by norm_num)]
  congr 1
  omega

end Erdos821.AnalyticSieve
