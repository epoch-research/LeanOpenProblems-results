import Submission.SharpSelbergWeights

/-!
# A two-dimensional sieve error of order z^(2+epsilon)

Uniformity in the coefficient and the finite set of sifting primes is
explicit. This improves an upper-sieve error; it is not a lower-bound
sieve or a settlement of the totient multiplicity conjecture.
-/

open Finset Filter
open scoped Classical BigOperators

namespace Erdos821.Sieve

set_option maxHeartbeats 3000000

lemma exists_card_pow_le_const_product_rpow (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : Finset ℕ, (∀ p ∈ S, 0 < p) →
      B ^ S.card ≤ C * (((∏ p ∈ S, p : ℕ) : ℝ) ^ ε) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)^ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨K, hK⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop B))
  refine ⟨B^K, pow_pos (by linarith) _, ?_⟩
  intro S hS
  have hpoint (p : ℕ) (hp : p ∈ S) :
      B ≤ (if p < K then B else 1) * (p : ℝ)^ε := by
    by_cases hpK : p < K
    · rw [if_pos hpK]
      exact le_mul_of_one_le_right (by linarith)
        (Real.one_le_rpow (by exact_mod_cast hS p hp) hε.le)
    · rw [if_neg hpK, one_mul]
      exact hK p (Nat.le_of_not_gt hpK)
  have hcard : (S.filter (fun p => p < K)).card ≤ K := by
    have hsub : S.filter (fun p => p < K) ⊆ range K := by
      intro p hp
      exact mem_range.mpr (mem_filter.mp hp).2
    simpa only [card_range] using card_le_card hsub
  calc
    B^S.card = ∏ _p ∈ S, B := (prod_const B).symm
    _ ≤ ∏ p ∈ S, ((if p < K then B else 1) * (p : ℝ)^ε) :=
      prod_le_prod (fun _ _ => by linarith) hpoint
    _ = B^(S.filter (fun p => p < K)).card * (((∏ p ∈ S, p : ℕ) : ℝ)^ε) := by
      rw [prod_mul_distrib, ← prod_filter, prod_const,
        Real.finset_prod_rpow S _ (fun p _ => Nat.cast_nonneg p), ← Nat.cast_prod]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB hcard)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma pair_local_product_le_six_pow (S : Finset ℕ) (hS : ∀ p ∈ S, 2 < p) :
    (∏ p ∈ S, (2 : ℝ)/(1-2/(p : ℝ))) ≤ 6^S.card := by
  rw [← prod_const]
  apply Finset.prod_le_prod
  · intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hS p hp
    have hfrac : (2 : ℝ)/(p : ℝ) ≤ 2/3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    exact div_nonneg (by norm_num) (by linarith)
  · intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hS p hp
    have hfrac : (2 : ℝ)/(p : ℝ) ≤ 2/3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < 1-2/(p : ℝ))).mpr
    linarith

lemma prime_product_sublevel_card_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℕ) :
    (P.powerset.filter (fun S => (∏ p ∈ S, p) ≤ z)).card ≤ z := by
  let W := P.powerset.filter (fun S => (∏ p ∈ S, p) ≤ z)
  have hmaps : Set.MapsTo (fun S : Finset ℕ => ∏ p ∈ S, p)
      (↑W : Set (Finset ℕ)) (↑(Finset.Icc 1 z) : Set ℕ) := by
    intro S hS
    obtain ⟨hSP, hSz⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_Icc.mpr ⟨Finset.prod_pos
      (fun p hp => (hP p (Finset.mem_powerset.mp hSP hp)).pos), hSz⟩
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) (↑W : Set (Finset ℕ)) := by
    intro S hS T hT heq
    have hSP := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    have hTP := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
    have h := congrArg Nat.primeFactors heq
    simpa only [Nat.primeFactors_prod (fun p hp => hP p (hSP hp)),
      Nat.primeFactors_prod (fun p hp => hP p (hTP hp))] using h
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card_of_injOn _ hmaps hinj

lemma pair_local_sum_le_const_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ 2 < p) →
      ∀ z : ℕ, 0 < z →
      (∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z,
        ∏ p ∈ S, (2 : ℝ)/(1-2/(p : ℝ))) ≤ C*(z : ℝ)^(1+ε) := by
  obtain ⟨C, hC, hCbound⟩ := exists_card_pow_le_const_product_rpow 6 ε (by norm_num) hε
  refine ⟨C, hC, ?_⟩
  intro P hP z hz
  let W := P.powerset.filter (fun S => (∏ p ∈ S, p) ≤ z)
  have hcard : (W.card : ℝ) ≤ z := by
    exact_mod_cast prime_product_sublevel_card_le P (fun p hp => (hP p hp).1) z
  have hterm (S : Finset ℕ) (hS : S ∈ W) :
      (∏ p ∈ S, (2 : ℝ)/(1-2/(p : ℝ))) ≤ C*(z : ℝ)^ε := by
    have hSP := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    calc
      _ ≤ 6^S.card := pair_local_product_le_six_pow S (fun p hp => (hP p (hSP hp)).2)
      _ ≤ C*(((∏ p ∈ S, p : ℕ) : ℝ)^ε) :=
        hCbound S (fun p hp => (hP p (hSP hp)).1.pos)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast (Finset.mem_filter.mp hS).2) hε.le) hC.le
  calc
    _ ≤ ∑ _S ∈ W, C*(z : ℝ)^ε := sum_le_sum hterm
    _ = (W.card : ℝ)*(C*(z : ℝ)^ε) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (z : ℝ)*(C*(z : ℝ)^ε) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [Real.rpow_add (by exact_mod_cast hz), Real.rpow_one]; ring

/-- The error estimate is uniform in P, which may grow with the sieve level. -/
theorem eventually_pair_local_error_le_rpow (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ z : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ 2 < p) →
      (∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z,
        ∏ p ∈ S, (2 : ℝ)/(1-2/(p : ℝ)))^2 ≤ (z : ℝ)^(2+δ) := by
  obtain ⟨C, hC, hbound⟩ := pair_local_sum_le_const_rpow (δ/4) (by linarith)
  have ht : Tendsto (fun z : ℕ => (z : ℝ)^(δ/2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < δ/2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (C^2)), eventually_ge_atTop 1]
    with z hzC hz
  intro P hP
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hnonneg : 0 ≤ ∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z,
      ∏ p ∈ S, (2 : ℝ)/(1-2/(p : ℝ)) := by
    apply sum_nonneg
    intro S hS
    apply prod_nonneg
    intro p hp
    have hpP := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1 hp
    have hpR : (2 : ℝ) < p := by exact_mod_cast (hP p hpP).2
    exact div_nonneg (by norm_num) (sub_nonneg.mpr
      ((div_le_one (by linarith : (0 : ℝ) < p)).mpr hpR.le))
  calc
    _ ≤ (C*(z : ℝ)^(1+δ/4))^2 :=
      pow_le_pow_left₀ hnonneg (hbound P hP z (by omega)) 2
    _ = C^2 * (z : ℝ)^(2+δ/2) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hz0.le]
      congr 2
      norm_num
      ring
    _ ≤ (z : ℝ)^(δ/2) * (z : ℝ)^(2+δ/2) :=
      mul_le_mul_of_nonneg_right hzC (Real.rpow_nonneg hz0.le _)
    _ = _ := by rw [← Real.rpow_add hz0]; congr 1; ring


lemma prime_pair_sieve_bound_local (N a z : ℕ) (hz : 1 ≤ z) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 2 < p ∧ p ≤ z ∧ ¬p ∣ a) :
    (((Finset.range N).filter (fun q => q.Prime ∧ (a * q + 1).Prime ∧
      z < q ∧ z < a * q + 1)).card : ℝ) ≤
      (N : ℝ) * (∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z,
        (∏ p ∈ S, (((2 : ℝ) / p)⁻¹ - 1))⁻¹)⁻¹ +
      (∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z,
        ∏ p ∈ S, (2 : ℝ)/(1-2/(p : ℝ))) ^ 2 := by
  let bad : ℕ → ℕ → Prop := fun p q => p ∣ q * (a * q + 1)
  have hcount : ∀ S ∈ P.powerset,
      |(((Finset.range N).filter (fun q => ∀ p ∈ S, bad p q)).card : ℝ) -
        (N : ℝ) * (∏ p ∈ S, (2 : ℝ) / p)| ≤ ∏ _p ∈ S, (2 : ℝ) := by
    intro S hS
    rw [Finset.prod_const]
    exact abs_card_pair_conditions N a S (fun p hp =>
      ⟨(hP p (Finset.mem_powerset.mp hS hp)).1,
        (hP p (Finset.mem_powerset.mp hS hp)).2.2.2⟩)
  have hb := finite_selberg_bound_local (Finset.range N) P (fun p hp => (hP p hp).1)
    bad (fun _ => (2 : ℝ)) (fun p hp => ⟨by norm_num, by
      change (2 : ℝ) < p
      exact_mod_cast (hP p hp).2.1⟩)
    N z hz hcount
  apply le_trans ?_ hb
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hqN, hqprime, hpairprime, hzq, hzaq⟩ := Finset.mem_filter.mp hq
  apply Finset.mem_filter.mpr
  refine ⟨hqN, ?_⟩
  intro p hp hbad
  obtain ⟨hpprime, _, hpz, _⟩ := hP p hp
  rcases hpprime.dvd_mul.mp hbad with hdiv | hdiv
  · have heq := (Nat.prime_dvd_prime_iff_eq hpprime hqprime).mp hdiv
    omega
  · have heq := (Nat.prime_dvd_prime_iff_eq hpprime hpairprime).mp hdiv
    omega

/-- A uniform two-dimensional sieve bound with an arbitrarily small
loss above the quadratic error exponent. -/
theorem eventually_prime_pair_sieve_bound (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ z : ℕ in atTop, ∀ (N a : ℕ) (P : Finset ℕ),
      (∀ p ∈ P, p.Prime ∧ 2 < p ∧ p ≤ z ∧ ¬p ∣ a) →
      (((Finset.range N).filter (fun q => q.Prime ∧ (a*q+1).Prime ∧
        z < q ∧ z < a*q+1)).card : ℝ) ≤
        (N : ℝ) * (∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z,
          (∏ p ∈ S, (((2 : ℝ)/p)⁻¹-1))⁻¹)⁻¹ + (z : ℝ)^(2+δ) := by
  filter_upwards [eventually_pair_local_error_le_rpow δ hδ, eventually_ge_atTop 1]
    with z hz hz1
  intro N a P hP
  exact (prime_pair_sieve_bound_local N a z hz1 P hP).trans
    (add_le_add le_rfl (hz P (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1⟩)))

end Erdos821.Sieve
