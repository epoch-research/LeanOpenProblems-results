import Submission.StrongMangoldt

/-!
# Removing nonsmooth predecessors from prime-modulus progressions

A large prime divisor of p-1 other than the progression modulus produces a
prime pair with a short cofactor. The Selberg bound controls these pairs on
average over the short cofactors.
-/

open scoped BigOperators
open Finset ArithmeticFunction Filter

namespace Erdos821.AnalyticSieve

noncomputable def primePairCofactorCount (X a : ℕ) : ℕ :=
  ((Finset.range (X / a + 1)).filter (fun q => q.Prime ∧ (a * q + 1).Prime)).card

lemma prime_pair_cofactor_bound (X a J : ℕ) (ha : 0 < a) (haX : a ≤ X) (hJ : 0 < J) :
    (primePairCofactorCount X a : ℝ) ≤
      (4 * (X : ℝ) / ((J : ℝ) * Real.log 2) ^ 2) *
        (((2 * (a : ℝ)) / Nat.totient (2 * a)) ^ 2 / (a : ℝ)) +
      ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) := by
  let D : ℝ := ((J : ℝ) * Real.log 2) ^ 2
  let E : ℝ := (2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1
  have hD : 0 < D := sq_pos_of_pos (mul_pos (by exact_mod_cast hJ) (Real.log_pos (by norm_num)))
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hN : ((X / a + 1 : ℕ) : ℝ) ≤ 2 * (X : ℝ) / a := by
    calc
      _ = ((X / a : ℕ) : ℝ) + 1 := by push_cast; rfl
      _ ≤ (X : ℝ) / a + 1 := add_le_add Nat.cast_div_le le_rfl
      _ ≤ (X : ℝ) / a + (X : ℝ) / a :=
        add_le_add le_rfl ((one_le_div haR).mpr (by exact_mod_cast haX))
      _ = _ := by ring
  have hb := Erdos821.Sieve.prime_pair_explicit_bound (X / a + 1) a J ha hJ
  have heq : 2 * ((X / a + 1 : ℕ) : ℝ) /
      (((Nat.totient (2 * a) : ℝ) / (2 * a) * J * Real.log 2) ^ 2) =
        2 * ((X / a + 1 : ℕ) : ℝ) * (((2 * (a : ℝ)) / Nat.totient (2 * a)) ^ 2) / D := by
    dsimp [D]
    simp only [mul_pow, div_pow, div_eq_mul_inv, mul_inv, inv_pow, inv_inv]
    ring
  rw [heq] at hb
  calc
    _ ≤ 2 * ((X / a + 1 : ℕ) : ℝ) * (((2 * (a : ℝ)) / Nat.totient (2 * a)) ^ 2) / D + E := by
      simpa only [primePairCofactorCount, E, add_assoc] using hb
    _ ≤ 2 * (2 * (X : ℝ) / a) * (((2 * (a : ℝ)) / Nat.totient (2 * a)) ^ 2) / D + E := by
      gcongr
    _ = _ := by dsimp [D, E]; ring

lemma totient_ratio_submultiplicative (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ((a * b : ℕ) : ℝ) / Nat.totient (a * b) ≤
      ((a : ℝ) / Nat.totient a) * ((b : ℝ) / Nat.totient b) := by
  have hφa : (0 : ℝ) < Nat.totient a := by exact_mod_cast Nat.totient_pos.mpr ha
  have hφb : (0 : ℝ) < Nat.totient b := by exact_mod_cast Nat.totient_pos.mpr hb
  have hφ : (Nat.totient a : ℝ) * Nat.totient b ≤ Nat.totient (a * b) := by
    exact_mod_cast Nat.totient_super_multiplicative a b
  calc
    _ ≤ ((a * b : ℕ) : ℝ) / ((Nat.totient a : ℝ) * Nat.totient b) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hφa hφb) hφ
    _ = _ := by push_cast; ring

lemma prime_totient_ratio_le_two {q : ℕ} (hq : q.Prime) :
    (q : ℝ) / Nat.totient q ≤ 2 := by
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq.pos
  apply (div_le_iff₀ hφ).mpr
  rw [Nat.totient_prime hq, Nat.cast_sub hq.one_le]
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  norm_num
  linarith

lemma prime_cofactor_totient_ratio_sq {q k : ℕ} (hq : q.Prime) (hk : 0 < k) :
    ((2 * ((q * k : ℕ) : ℝ)) / Nat.totient (2 * (q * k))) ^ 2 ≤
      4 * ((2 * (k : ℝ)) / Nat.totient (2 * k)) ^ 2 := by
  have h := totient_ratio_submultiplicative q (2 * k) hq.pos (by omega)
  have heq : q * (2 * k) = 2 * (q * k) := by ring
  rw [heq] at h
  have hratio : (2 * ((q * k : ℕ) : ℝ)) / Nat.totient (2 * (q * k)) ≤
      2 * ((2 * (k : ℝ)) / Nat.totient (2 * k)) := by
    calc
      _ = ((q * (2 * k) : ℕ) : ℝ) / Nat.totient (2 * (q * k)) := by push_cast; ring
      _ ≤ ((q : ℝ) / Nat.totient q) * (((2 * k : ℕ) : ℝ) / Nat.totient (2 * k)) := by
        simpa only [heq] using h
      _ ≤ _ := by push_cast; gcongr; exact prime_totient_ratio_le_two hq
  have hsq := pow_le_pow_left₀ (by positivity) hratio 2
  simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hsq

lemma sum_prime_pair_prime_cofactor_bound (X K J q : ℕ) (hq : q.Prime)
    (hKX : q * K ≤ X) (hJ : 0 < J) :
    (∑ k ∈ Finset.Icc 1 K, (primePairCofactorCount X (q * k) : ℝ)) ≤
      (64 * Erdos821.Sieve.totientRatioAverageConstant * (X : ℝ) * (harmonic K : ℝ) /
        ((J : ℝ) * Real.log 2) ^ 2) / q +
      (K : ℝ) * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) := by
  let D : ℝ := ((J : ℝ) * Real.log 2) ^ 2
  let E : ℝ := (2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1
  have hD : 0 < D := sq_pos_of_pos (mul_pos (by exact_mod_cast hJ) (Real.log_pos (by norm_num)))
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hb (k : ℕ) (hk : k ∈ Finset.Icc 1 K) :
      (primePairCofactorCount X (q * k) : ℝ) ≤
        (16 * (X : ℝ) / (D * q)) *
          (((2 * (k : ℝ)) / Nat.totient (2 * k)) ^ 2 / (k : ℝ)) + E := by
    have hk0 : 0 < k := (mem_Icc.mp hk).1
    have hkX : q * k ≤ X := (Nat.mul_le_mul_left q (mem_Icc.mp hk).2).trans hKX
    have hp := prime_pair_cofactor_bound X (q * k) J (Nat.mul_pos hq.pos hk0) hkX hJ
    apply hp.trans
    calc
      _ ≤ (4 * (X : ℝ) / D) *
          ((4 * ((2 * (k : ℝ)) / Nat.totient (2 * k)) ^ 2) / ((q * k : ℕ) : ℝ)) + E := by
        gcongr
        exact prime_cofactor_totient_ratio_sq hq hk0
      _ = _ := by push_cast; ring
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ((16 * (X : ℝ) / (D * q)) *
        (((2 * (k : ℝ)) / Nat.totient (2 * k)) ^ 2 / (k : ℝ)) + E) := sum_le_sum hb
    _ = (16 * (X : ℝ) / (D * q)) *
        (∑ k ∈ Finset.Icc 1 K, ((2 * (k : ℝ)) / Nat.totient (2 * k)) ^ 2 / (k : ℝ)) + (K : ℝ) * E := by
      rw [sum_add_distrib, ← Finset.mul_sum]
      simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
    _ ≤ (16 * (X : ℝ) / (D * q)) *
        (4 * Erdos821.Sieve.totientRatioAverageConstant * (harmonic K : ℝ)) + (K : ℝ) * E :=
      add_le_add (mul_le_mul_of_nonneg_left
        (Erdos821.Sieve.totient_ratio_two_mul_harmonic_average K) (by positivity)) le_rfl
    _ = _ := by dsimp [D, E]; ring

noncomputable def roughProgressionPrimes (q Y X : ℕ) : Finset ℕ :=
  (X + 1).primesBelow.filter (fun p => q ∣ p - 1 ∧ p - 1 ∉ Nat.smoothNumbers Y)

lemma rough_progression_card_le_pairs (X K Y q : ℕ) (hq : q.Prime) (hqY : q < Y)
    (hX : X ≤ q * K * Y) :
    (roughProgressionPrimes q Y X).card ≤
      ∑ k ∈ Finset.Icc 1 K, primePairCofactorCount X (q * k) := by
  classical
  let P : ℕ → Finset ℕ := fun k =>
    (Finset.range (X / (q * k) + 1)).filter (fun ℓ => ℓ.Prime ∧ (q * k * ℓ + 1).Prime)
  have hsub : roughProgressionPrimes q Y X ⊆
      (Finset.Icc 1 K).biUnion (fun k => (P k).image (fun ℓ => q * k * ℓ + 1)) := by
    intro p hp
    obtain ⟨hpX, hqdvd, hpns⟩ := mem_filter.mp hp
    obtain ⟨hpX, hprime⟩ := Nat.mem_primesBelow.mp hpX
    have hpred : 0 < p - 1 := Nat.sub_pos_of_lt hprime.one_lt
    have hnot : ¬∀ ℓ, ℓ.Prime → ℓ ∣ p - 1 → ℓ < Y :=
      fun h => hpns (Nat.mem_smoothNumbers'.mpr h)
    push_neg at hnot
    obtain ⟨ℓ, hℓ, hℓdvd, hYℓ⟩ := hnot
    let a := (p - 1) / ℓ
    have ha : 0 < a := Nat.div_pos (Nat.le_of_dvd hpred hℓdvd) hℓ.pos
    have haeq : a * ℓ = p - 1 := Nat.div_mul_cancel hℓdvd
    have hqℓ : ¬q ∣ ℓ := by
      intro h
      have heq : q = ℓ := (Nat.dvd_prime hℓ).mp h |>.resolve_left hq.ne_one
      omega
    have hqa : q ∣ a := (hq.dvd_mul.mp (haeq ▸ hqdvd)).resolve_right hqℓ
    let k := a / q
    have hk : 0 < k := Nat.div_pos (Nat.le_of_dvd ha hqa) hq.pos
    have hkq : q * k = a := Nat.mul_div_cancel' hqa
    have hmul : q * k * ℓ = p - 1 := by rw [hkq, haeq]
    have hkK : k ≤ K := by
      have hmul' : q * k * Y ≤ q * K * Y :=
        (Nat.mul_le_mul_left (q * k) hYℓ).trans (by omega)
      have hqk : q * k ≤ q * K := Nat.le_of_mul_le_mul_right hmul' (by omega : 0 < Y)
      exact Nat.le_of_mul_le_mul_left hqk hq.pos
    have hℓX : ℓ ≤ X / (q * k) := (Nat.le_div_iff_mul_le (Nat.mul_pos hq.pos hk)).mpr (by
      rw [mul_comm ℓ (q * k), hmul]
      omega)
    apply mem_biUnion.mpr
    refine ⟨k, mem_Icc.mpr ⟨hk, hkK⟩, mem_image.mpr ⟨ℓ, ?_, by omega⟩⟩
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (by omega), hℓ, ?_⟩
    convert hprime using 1 <;> omega
  calc
    _ ≤ ((Finset.Icc 1 K).biUnion (fun k => (P k).image (fun ℓ => q * k * ℓ + 1))).card := card_le_card hsub
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ((P k).image (fun ℓ => q * k * ℓ + 1)).card := card_biUnion_le
    _ ≤ _ := sum_le_sum (fun _ _ => card_image_le)

lemma rough_progression_prime_count_le (X K Y J q : ℕ) (hq : q.Prime) (hqY : q < Y)
    (hX : X ≤ q * K * Y) (hKX : q * K ≤ X) (hJ : 0 < J) :
    ((roughProgressionPrimes q Y X).card : ℝ) ≤
      (64 * Erdos821.Sieve.totientRatioAverageConstant * (X : ℝ) * (harmonic K : ℝ) /
        ((J : ℝ) * Real.log 2) ^ 2) / q +
      (K : ℝ) * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) := by
  have hc : ((roughProgressionPrimes q Y X).card : ℝ) ≤
      ∑ k ∈ Finset.Icc 1 K, (primePairCofactorCount X (q * k) : ℝ) := by
    exact_mod_cast rough_progression_card_le_pairs X K Y q hq hqY hX
  exact hc.trans (sum_prime_pair_prime_cofactor_bound X K J q hq hKX hJ)

lemma rough_witness_card_le_sum (M : Finset ℕ+) (B Y N : ℕ) :
    ((shiftedWitnessPrimes M B N).filter (fun p => p - 1 ∉ Nat.smoothNumbers Y)).card ≤
      ∑ q ∈ M, (roughProgressionPrimes q Y N).card := by
  classical
  have hsub : (shiftedWitnessPrimes M B N).filter (fun p => p - 1 ∉ Nat.smoothNumbers Y) ⊆
      M.biUnion (fun q => roughProgressionPrimes q Y N) := by
    intro p hp
    obtain ⟨hpW, hpns⟩ := mem_filter.mp hp
    obtain ⟨hpI, hprime, _, q, hqM, hqres⟩ := mem_filter.mp hpW
    refine mem_biUnion.mpr ⟨q, hqM, mem_filter.mpr ⟨?_, ?_, hpns⟩⟩
    · exact Nat.mem_primesBelow.mpr ⟨by have := (mem_Icc.mp hpI).2; omega, hprime⟩
    · exact (residue_one_iff_dvd_pred hprime.pos).mp hqres
  exact (card_le_card hsub).trans card_biUnion_le

/-- The cost of rejecting nonsmooth predecessors is proportional to the same
reciprocal-modulus sum occurring in the progression main term. -/
theorem rough_witness_prime_count_le (M : Finset ℕ+) (D Q B Y N K J : ℕ)
    (hM : ∀ q ∈ M, (q : ℕ).Prime ∧ D ≤ (q : ℕ) ∧ (q : ℕ) ≤ Q)
    (hQY : Q < Y) (hN : N ≤ D * K * Y) (hK : Q * K ≤ N) (hJ : 0 < J) :
    (((shiftedWitnessPrimes M B N).filter (fun p => p - 1 ∉ Nat.smoothNumbers Y)).card : ℝ) ≤
      (64 * Erdos821.Sieve.totientRatioAverageConstant * (N : ℝ) * (harmonic K : ℝ) /
        ((J : ℝ) * Real.log 2) ^ 2) * (∑ q ∈ M, (((q : ℕ).totient : ℝ))⁻¹) +
      (M.card : ℝ) * K * ((2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1) := by
  let A : ℝ := 64 * Erdos821.Sieve.totientRatioAverageConstant * (N : ℝ) * (harmonic K : ℝ) /
    ((J : ℝ) * Real.log 2) ^ 2
  let E : ℝ := (2 : ℝ) ^ (64 * J) + (2 : ℝ) ^ (16 * J) + 1
  have hA : 0 ≤ A := by
    have hH := harmonic_real_nonneg K
    dsimp [A, Erdos821.Sieve.totientRatioAverageConstant]
    positivity
  have hbound (q : ℕ+) (hq : q ∈ M) : ((roughProgressionPrimes q Y N).card : ℝ) ≤
      A * (((q : ℕ).totient : ℝ))⁻¹ + (K : ℝ) * E := by
    have hqd := hM q hq
    have hb := rough_progression_prime_count_le N K Y J q hqd.1 (lt_of_le_of_lt hqd.2.2 hQY)
      (hN.trans (Nat.mul_le_mul_right Y (Nat.mul_le_mul_right K hqd.2.1)))
      ((Nat.mul_le_mul_right K hqd.2.2).trans hK) hJ
    apply hb.trans
    have hφ : (0 : ℝ) < (q : ℕ).totient := by exact_mod_cast Nat.totient_pos.mpr q.pos
    have hφq : ((q : ℕ).totient : ℝ) ≤ (q : ℕ) := by exact_mod_cast Nat.totient_le (q : ℕ)
    simpa only [div_eq_mul_inv] using
      add_le_add (div_le_div_of_nonneg_left hA hφ hφq) (le_refl ((K : ℝ) * E))
  have hc : (((shiftedWitnessPrimes M B N).filter (fun p => p - 1 ∉ Nat.smoothNumbers Y)).card : ℝ) ≤
      ∑ q ∈ M, ((roughProgressionPrimes q Y N).card : ℝ) := by
    exact_mod_cast rough_witness_card_le_sum M B Y N
  apply hc.trans ((sum_le_sum hbound).trans_eq _)
  rw [sum_add_distrib, ← Finset.mul_sum]
  simp only [sum_const, nsmul_eq_mul]
  dsimp [A, E]
  ring

end Erdos821.AnalyticSieve
