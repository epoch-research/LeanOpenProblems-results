import Submission.ProgressionScales
import Submission.Sieve

/-!
# An unconditional supply of weighted prime-modulus progressions

The elementary dyadic Chebyshev lower bound populates a wide interval of
prime moduli. Together with the power-saving progression error, it gives
an unconditional lower bound on the total residue-one von Mangoldt weight.
-/

open scoped BigOperators
open Finset ArithmeticFunction Filter

namespace Erdos821.AnalyticSieve

def primeModuliBetween (D Q : ℕ) : Finset ℕ+ :=
  (Icc 1 (⟨Q + 1, by omega⟩ : ℕ+)).filter (fun q => (q : ℕ).Prime ∧ D ≤ (q : ℕ) ∧ (q : ℕ) ≤ Q)

lemma mem_primeModuliBetween {D Q : ℕ} {q : ℕ+} :
    q ∈ primeModuliBetween D Q ↔ (q : ℕ).Prime ∧ D ≤ (q : ℕ) ∧ (q : ℕ) ≤ Q := by
  simp only [primeModuliBetween, mem_filter, mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨q.pos, by change (q : ℕ) ≤ Q + 1; omega⟩, h⟩

lemma card_primeModuliBetween (D Q : ℕ) :
    (primeModuliBetween D Q).card = ((Q + 1).primesBelow.filter (fun p => D ≤ p)).card := by
  apply Finset.card_bij (fun (q : ℕ+) _ => (q : ℕ))
  · intro q hq
    obtain ⟨hp, hD, hQ⟩ := mem_primeModuliBetween.mp hq
    exact mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega, hp⟩, hD⟩
  · intro q hq r hr h
    exact PNat.coe_injective h
  · intro p hp
    obtain ⟨hp, hD⟩ := mem_filter.mp hp
    obtain ⟨hQ, hprime⟩ := Nat.mem_primesBelow.mp hp
    refine ⟨⟨p, hprime.pos⟩, ?_, rfl⟩
    exact mem_primeModuliBetween.mpr ⟨hprime, hD, by change p ≤ Q; omega⟩

lemma primesBelow_card_le_moduli_add (D Q : ℕ) :
    (Q + 1).primesBelow.card ≤ (primeModuliBetween D Q).card + D := by
  have hs : (Q + 1).primesBelow ⊆ ((Q + 1).primesBelow.filter (fun p => D ≤ p)) ∪ range D := by
    intro p hp
    by_cases h : D ≤ p
    · exact mem_union_left _ (mem_filter.mpr ⟨hp, h⟩)
    · exact mem_union_right _ (mem_range.mpr (by omega))
  calc
    _ ≤ (((Q + 1).primesBelow.filter (fun p => D ≤ p)) ∪ range D).card := Finset.card_le_card hs
    _ ≤ _ := by
      rw [card_primeModuliBetween]
      simpa only [Finset.card_range] using Finset.card_union_le
        ((Q + 1).primesBelow.filter (fun p => D ≤ p)) (range D)

lemma dyadic_prime_count_bound (t : ℕ) (ht : 1 ≤ t) :
    2 ^ t ≤ t * ((2 ^ t + 1).primesBelow.card + 1) := by
  simpa only [Nat.sub_add_cancel ht] using Erdos821.Sieve.dyadic_prime_count_lower (t - 1)

lemma progression_scale_moduli_count {s L : ℕ} (hL : 1 ≤ L) (hLs : L ≤ s)
    (hsmall : 128 * s ≤ 2 ^ L) :
    progressionScaleQ s L ≤ 64 * s *
      (primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L)).card := by
  let t := 32 * s - 2 * L
  let D := progressionScaleD s L
  let Q := progressionScaleQ s L
  let M := primeModuliBetween D Q
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hD : 1 ≤ D := by dsimp [D, progressionScaleD]; exact one_le_pow₀ (by norm_num)
  have hDQ : D * 2 ^ L = Q := by
    dsimp [D, Q, progressionScaleD, progressionScaleQ]
    rw [← pow_add]
    congr 1
    omega
  have hcheb : Q ≤ t * ((Q + 1).primesBelow.card + 1) := dyadic_prime_count_bound t ht
  have hcard : (Q + 1).primesBelow.card ≤ M.card + D := primesBelow_card_le_moduli_add D Q
  have hsmall' : 2 * t * (D + 1) ≤ Q := by
    calc
      _ ≤ 128 * s * D := by dsimp [t]; nlinarith [Nat.sub_le (32 * s) (2 * L)]
      _ ≤ 2 ^ L * D := Nat.mul_le_mul_right D hsmall
      _ = Q := by rw [mul_comm]; exact hDQ
  have hq : Q ≤ 2 * t * M.card := by nlinarith
  change Q ≤ 64 * s * M.card
  have htc : 2 * t ≤ 64 * s := by dsimp [t]; omega
  exact hq.trans (Nat.mul_le_mul_right M.card htc)

lemma moduli_reciprocal_ge_card (D Q : ℕ) (_hQ : 0 < Q) :
    ((primeModuliBetween D Q).card : ℝ) / Q ≤
      ∑ q ∈ primeModuliBetween D Q, (((q : ℕ).totient : ℝ))⁻¹ := by
  calc
    _ = ∑ q ∈ primeModuliBetween D Q, (1 : ℝ) / Q := by simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      have h := mem_primeModuliBetween.mp hq
      have hφ : (0 : ℝ) < (q : ℕ).totient := by exact_mod_cast Nat.totient_pos.mpr q.pos
      have hφQ : ((q : ℕ).totient : ℝ) ≤ Q := by
        exact_mod_cast (Nat.totient_le (q : ℕ)).trans h.2.2
      simpa only [one_div] using div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num) hφ hφQ

lemma mangoldtSum_nonneg (N : ℕ) : 0 ≤ mangoldtSum N :=
  Finset.sum_nonneg (fun _ _ => vonMangoldt_nonneg)

lemma primesBelow_log_two_le_mangoldt (N : ℕ) :
    Real.log 2 * ((N + 1).primesBelow.card : ℝ) ≤ mangoldtSum N := by
  calc
    _ = ∑ p ∈ (N + 1).primesBelow, Real.log 2 := by simp [mul_comm]
    _ ≤ ∑ p ∈ (N + 1).primesBelow, vonMangoldt p := by
      apply Finset.sum_le_sum
      intro p hp
      have hprime := (Nat.mem_primesBelow.mp hp).2
      rw [vonMangoldt_apply_prime hprime]
      exact log_nat_mono hprime.two_le
    _ ≤ mangoldtSum N := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hpN, hp⟩ := Nat.mem_primesBelow.mp hp
        exact mem_Icc.mpr ⟨hp.pos, by omega⟩
      · exact fun _ _ _ => vonMangoldt_nonneg

lemma dyadic_mangoldt_lower (t : ℕ) (ht : 1 ≤ t) :
    ((2 ^ t : ℕ) : ℝ) ≤ 4 * (t : ℝ) * mangoldtSum (2 ^ t) := by
  have hN : 2 ≤ 2 ^ t := by simpa only [pow_one] using Nat.pow_le_pow_right (by norm_num : 0 < 2) ht
  have hcard : 1 ≤ (2 ^ t + 1).primesBelow.card := by
    apply Nat.succ_le_iff.mpr
    exact Finset.card_pos.mpr ⟨2, Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩⟩
  have hcount : 2 ^ t ≤ 2 * t * (2 ^ t + 1).primesBelow.card := by
    have h := dyadic_prime_count_bound t ht
    nlinarith
  have hweight := primesBelow_log_two_le_mangoldt (2 ^ t)
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hw : ((2 ^ t + 1).primesBelow.card : ℝ) ≤ 2 * mangoldtSum (2 ^ t) := by
    have h := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg (α := ℝ) (2 ^ t + 1).primesBelow.card)
    linarith
  have hc : ((2 ^ t : ℕ) : ℝ) ≤ 2 * (t : ℝ) * ((2 ^ t + 1).primesBelow.card : ℝ) := by exact_mod_cast hcount
  have hm := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 2 * (t : ℝ))
  nlinarith

lemma progression_scale_main_lower {s L : ℕ} (hL : 1 ≤ L) (hLs : L ≤ s)
    (hsmall : 128 * s ≤ 2 ^ L) :
    (progressionScaleN s : ℝ) / (16384 * (s : ℝ) ^ 2) ≤
      mangoldtSum (progressionScaleN s) *
        (∑ q ∈ primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L),
          (((q : ℕ).totient : ℝ))⁻¹) := by
  have hs : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hQ : (0 : ℝ) < progressionScaleQ s L := by unfold progressionScaleQ; positivity
  have hψ : (progressionScaleN s : ℝ) / (256 * (s : ℝ)) ≤ mangoldtSum (progressionScaleN s) := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h := dyadic_mangoldt_lower (64 * s) (by omega)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    change (progressionScaleN s : ℝ) ≤ 4 * (64 * (s : ℝ)) * mangoldtSum (progressionScaleN s) at h
    nlinarith
  have hrecip : 1 / (64 * (s : ℝ)) ≤
      ∑ q ∈ primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L),
        (((q : ℕ).totient : ℝ))⁻¹ := by
    apply le_trans _ (moduli_reciprocal_ge_card _ _ (by unfold progressionScaleQ; positivity))
    apply (div_le_div_iff₀ (by positivity) hQ).mpr
    have h := progression_scale_moduli_count hL hLs hsmall
    have hc : (progressionScaleQ s L : ℝ) ≤ 64 * (s : ℝ) *
        ((primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L)).card : ℝ) := by exact_mod_cast h
    nlinarith
  calc
    _ = ((progressionScaleN s : ℝ) / (256 * (s : ℝ))) * (1 / (64 * (s : ℝ))) := by field_simp; ring
    _ ≤ _ := mul_le_mul hψ hrecip (by positivity) (mangoldtSum_nonneg _)

lemma progression_scale_error_small {s L : ℕ} (hL : 1 ≤ L) (hLs : L ≤ s)
    (hsmall : 32768000000000000 * (s + 1) ^ 7 ≤ 2 ^ L) :
    primeProgressionError (progressionScaleU s) (progressionScaleU s) (progressionScaleN s)
      (progressionScaleQ s L) (progressionScaleD s L) ≤ (progressionScaleN s : ℝ) / (32768 * (s : ℝ) ^ 2) := by
  have hs : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hN : (0 : ℝ) < progressionScaleN s := by unfold progressionScaleN; positivity
  have hsmall' : 32768000000000000 * ((s : ℝ) + 1) ^ 7 ≤ (2 : ℝ) ^ L := by exact_mod_cast hsmall
  have hbound : 1000000000000 * ((s : ℝ) + 1) ^ 5 / (2 : ℝ) ^ L ≤ 1 / (32768 * (s : ℝ) ^ 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      _ ≤ 32768000000000000 * ((s : ℝ) + 1) ^ 7 := by
        have hpow := pow_le_pow_left₀ hs.le (show (s : ℝ) ≤ (s : ℝ) + 1 by linarith) 2
        have h := mul_le_mul_of_nonneg_left hpow
          (by positivity : 0 ≤ 32768000000000000 * ((s : ℝ) + 1) ^ 5)
        nlinarith
      _ ≤ _ := by simpa only [one_mul] using hsmall'
  have h := (progression_scales_error_div_bound hLs).trans hbound
  have h' := (div_le_iff₀ hN).mp h
  convert h' using 1; ring

/-- A finite unconditional lower bound once the displayed elementary
polynomial-versus-exponential inequality holds. -/
theorem progression_scale_weight_lower {s L : ℕ} (hL : 1 ≤ L) (hLs : L ≤ s)
    (hsmall : 32768000000000000 * (s + 1) ^ 7 ≤ 2 ^ L) :
    (progressionScaleN s : ℝ) / (32768 * (s : ℝ) ^ 2) ≤
      ∑ q ∈ primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L),
        residueOneMangoldt q (progressionScaleN s) := by
  have hs : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hcount : 128 * s ≤ 2 ^ L := by
    have hp := Nat.pow_le_pow_right (show 0 < s + 1 by omega) (show 1 ≤ 7 by norm_num)
    simp only [pow_one] at hp
    omega
  have hmain := progression_scale_main_lower hL hLs hcount
  have herr := progression_scale_error_small hL hLs hsmall
  have hbal := progression_scales_balanced hL hLs
  have htotal := prime_progression_total_lower
    (primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L))
    (progressionScaleD s L) (progressionScaleQ s L)
    (by unfold progressionScaleD; positivity) (by unfold progressionScaleQ; positivity)
    (fun q hq => mem_primeModuliBetween.mp hq) (progressionScaleU s) (progressionScaleU s) (progressionScaleN s)
    (by unfold progressionScaleU; exact one_le_pow₀ (by norm_num))
    (hbal.trans (Nat.mul_le_mul_right _ (Nat.le_succ _))) hbal
  have heq : (progressionScaleN s : ℝ) / (16384 * (s : ℝ) ^ 2) =
      2 * ((progressionScaleN s : ℝ) / (32768 * (s : ℝ) ^ 2)) := by field_simp; ring
  rw [heq] at hmain
  linarith

/-- The polynomial side condition holds eventually for every fixed r>=1. -/
theorem eventually_progression_scale_weight_lower (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ L : ℕ in atTop,
      (progressionScaleN (r * L) : ℝ) / (32768 * ((r * L : ℕ) : ℝ) ^ 2) ≤
        ∑ q ∈ primeModuliBetween (progressionScaleD (r * L) L) (progressionScaleQ (r * L) L),
          residueOneMangoldt q (progressionScaleN (r * L)) := by
  filter_upwards [eventually_nat_poly_le_two_pow r 32768000000000000 7, eventually_ge_atTop 1] with L hpoly hL
  exact progression_scale_weight_lower hL (by nlinarith) hpoly

end Erdos821.AnalyticSieve
