import Submission.SharpSieveDenominator

/-!
# A sharper explicit prime-pair sieve bound

The new error and denominator estimates give a sixteen-fold reduction of
the main coefficient at the original error scale. No lower moment or
arbitrary-root smooth-prime theorem is asserted here.
-/

open Finset Filter
open scoped Classical BigOperators
namespace Erdos821.Sieve
set_option maxHeartbeats 3000000

theorem eventually_prime_pair_explicit_sharp :
    ∀ᶠ L : ℕ in atTop, ∀ N a : ℕ, 0 < a →
    (((Finset.range N).filter (fun q => q.Prime ∧ (a * q + 1).Prime)).card : ℝ) ≤
      2 * (N : ℝ) /
        (((Nat.totient (2 * a) : ℝ) / (2 * a) * L * Real.log 2) ^ 2) +
      (2 : ℝ) ^ (15 * L) + (2 : ℝ) ^ (6 * L) + 1 := by
  have ht : Tendsto (fun L : ℕ => 2^(6*L)) atTop atTop := by
    apply tendsto_atTop_mono (fun L => ?_) tendsto_id
    change L ≤ 2^(6*L)
    exact (Nat.lt_two_pow_self (n := L)).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  filter_upwards [ht.eventually (eventually_prime_pair_sieve_bound (1/2) (by norm_num)),
    eventually_ge_atTop 4] with L hpair hL
  intro N a ha
  let z : ℕ := 2 ^ (6 * L)
  let P := (2 ^ L + 1).primesBelow \ (2 * a).primeFactors
  have hM : 0 < 2 * a := by omega
  have hz : 1 ≤ z := Nat.one_le_pow _ _ (by decide)
  have hyz : 2 ^ L ≤ z := Nat.pow_le_pow_right (by decide) (by omega)
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ 2 < p ∧ p ≤ z ∧ ¬p ∣ a := by
    obtain ⟨hpQ, hpM⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpL, hprime⟩ := Nat.mem_primesBelow.mp hpQ
    have hp2 : p ≠ 2 := by
      intro heq
      subst p
      exact hpM (Nat.prime_two.mem_primeFactors (dvd_mul_right 2 a) hM.ne')
    refine ⟨hprime, by have := hprime.two_le; omega, by omega, ?_⟩
    intro hpa
    exact hpM (hprime.mem_primeFactors (dvd_mul_of_dvd_right hpa 2) hM.ne')
  let G := ∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z,
    (∏ p ∈ S, (((2 : ℝ) / p)⁻¹ - 1))⁻¹
  let B : ℝ := (Nat.totient (2 * a) : ℝ) / (2 * a) * L * Real.log 2
  have hB : 0 < B := by
    apply mul_pos
    · apply mul_pos
      · exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hM) (by positivity)
      · exact_mod_cast (show 0 < L by omega)
    · exact Real.log_pos (by norm_num)
  have hG : B ^ 2 / 2 ≤ G := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      pair_sieve_denominator_log_lower_sharp L (2 * a) hL hM (dvd_mul_right 2 a)
  have hGpos : 0 < G := (div_pos (sq_pos_of_pos hB) (by norm_num)).trans_le hG
  have hInv : G⁻¹ ≤ 2 / B ^ 2 := by
    rw [← inv_div]
    exact (inv_le_inv₀ hGpos (div_pos (sq_pos_of_pos hB) (by norm_num))).mpr hG
  have hb := hpair N a P hP
  let T := (Finset.range N).filter (fun q => q.Prime ∧ (a * q + 1).Prime ∧
    z < q ∧ z < a * q + 1)
  have hT : (T.card : ℝ) ≤ 2 * (N : ℝ) / B ^ 2 + (z : ℝ) ^ (2+1/2 : ℝ) := by
    calc
      (T.card : ℝ) ≤ (N : ℝ) * G⁻¹ + (z : ℝ) ^ (2+1/2 : ℝ) := hb
      _ ≤ (N : ℝ) * (2 / B ^ 2) + (z : ℝ) ^ (2+1/2 : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hInv (Nat.cast_nonneg N)) le_rfl
      _ = _ := by ring
  let S := (Finset.range N).filter (fun q => q.Prime ∧ (a * q + 1).Prime)
  have hsub : S ⊆ T ∪ Finset.range (z + 1) := by
    intro q hq
    obtain ⟨hqN, hqp, haqp⟩ := Finset.mem_filter.mp hq
    by_cases hzq : z < q
    · apply Finset.mem_union_left
      have hqaq : q ≤ a * q := Nat.le_mul_of_pos_left _ ha
      exact Finset.mem_filter.mpr ⟨hqN, hqp, haqp, hzq, by omega⟩
    · exact Finset.mem_union_right _ (Finset.mem_range.mpr (by omega))
  have hcard : S.card ≤ T.card + (z + 1) := by
    simpa only [Finset.card_range] using (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hzpow : (z : ℝ) ^ (2+1/2 : ℝ) = (2 : ℝ) ^ (15 * L) := by
    dsimp [z]
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by norm_num),
      ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  calc
    (S.card : ℝ) ≤ (T.card : ℝ) + ((z + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ (2 * (N : ℝ) / B ^ 2 + (z : ℝ) ^ (2+1/2 : ℝ)) + ((z + 1 : ℕ) : ℝ) :=
      add_le_add hT le_rfl
    _ = _ := by rw [hzpow]; dsimp [B, z]; push_cast; ring

lemma sharp_pair_error_rescale (J : ℕ) (hJ : 0 < J) :
    (2 : ℝ)^(60*J) + (2 : ℝ)^(24*J) ≤ (2 : ℝ)^(64*J) := by
  calc
    _ ≤ (2 : ℝ)^(60*J) + (2 : ℝ)^(60*J) := by
      exact add_le_add le_rfl (pow_le_pow_right₀ (by norm_num)
        (show 24*J ≤ 60*J by omega))
    _ = (2 : ℝ)^(60*J+1) := by rw [pow_succ]; ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)

/-- The threshold in J is absolute, independent of N and a. -/
theorem eventually_prime_pair_explicit_gain_sixteen :
    ∀ᶠ J : ℕ in atTop, ∀ N a : ℕ, 0 < a →
      (((Finset.range N).filter (fun q => q.Prime ∧ (a*q+1).Prime)).card : ℝ) ≤
        (N : ℝ)/(8*(((Nat.totient (2*a) : ℝ)/(2*a)*J*Real.log 2)^2)) +
          (2 : ℝ)^(64*J) + 1 := by
  have ht : Tendsto (fun J : ℕ => 4*J) atTop atTop := by
    apply tendsto_atTop_mono (fun J => ?_) tendsto_id
    change J ≤ 4*J
    omega
  filter_upwards [ht.eventually eventually_prime_pair_explicit_sharp,
    eventually_ge_atTop 1] with J hpair hJ
  intro N a ha
  have hh := hpair N a ha
  have hid : 2*(N : ℝ)/
      (((Nat.totient (2*a) : ℝ)/(2*a)*(4*J : ℕ)*Real.log 2)^2) =
        (N : ℝ)/(8*(((Nat.totient (2*a) : ℝ)/(2*a)*J*Real.log 2)^2)) := by
    push_cast
    ring
  rw [hid, show 15*(4*J) = 60*J by ring, show 6*(4*J) = 24*J by ring] at hh
  have he := sharp_pair_error_rescale J hJ
  linarith only [hh,he]

end Erdos821.Sieve
