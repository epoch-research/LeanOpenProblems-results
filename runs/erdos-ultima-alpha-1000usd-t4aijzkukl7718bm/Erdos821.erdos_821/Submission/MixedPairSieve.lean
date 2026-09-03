import Submission.HyperbolicPrimePairBound

/-!
# Prime-pair sieving with the exact local root count

A prime dividing the linear coefficient contributes one root rather than
being omitted. The error bound remains uniform in that coefficient.
-/

open Nat Finset Filter
open scoped Classical BigOperators
namespace Erdos821.Sieve
set_option maxHeartbeats 3000000

def pairRootMultiplicity (a p : ℕ) : ℕ := if p ∣ a then 1 else 2

lemma quadraticRootCount_prime_dvd (a p : ℕ) (hpa : p ∣ a) :
    quadraticRootCount a p = 1 := by
  have ha : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff a p).mpr hpa
  change {x : ZMod p | x*((a : ZMod p)*x+1)=0}.ncard = 1
  simp [ha]

lemma quadraticRootCount_prime_mixed (a p : ℕ) (hp : p.Prime) :
    quadraticRootCount a p = pairRootMultiplicity a p := by
  by_cases hpa : p ∣ a
  · simpa only [pairRootMultiplicity, if_pos hpa] using quadraticRootCount_prime_dvd a p hpa
  · simpa only [pairRootMultiplicity, if_neg hpa] using quadraticRootCount_prime a p hp hpa

lemma quadraticRootCount_product_mixed (a : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    quadraticRootCount a (∏ p ∈ P, p) = ∏ p ∈ P, pairRootMultiplicity a p := by
  induction P using Finset.induction_on with
  | empty => simp [quadraticRootCount_one]
  | @insert p P hpP ih =>
    have hp := hP p (mem_insert_self _ _)
    have hrest : ∀ q ∈ P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have hcop : p.Coprime (∏ q ∈ P, q) := Nat.coprime_prod_right_iff.mpr (by
      intro q hq
      exact (Nat.coprime_primes hp (hrest q hq)).mpr (fun he => hpP (he ▸ hq)))
    rw [prod_insert hpP, quadraticRootCount_mul a p _ hcop,
      quadraticRootCount_prime_mixed a p hp, ih hrest, prod_insert hpP]

lemma pairRootMultiplicity_properties (a p : ℕ) (ha : 2 ∣ a) (hp : p.Prime) :
    1 ≤ pairRootMultiplicity a p ∧ pairRootMultiplicity a p ≤ 2 ∧
      pairRootMultiplicity a p < p := by
  have hp2 := hp.two_le
  by_cases hpa : p ∣ a
  · simp only [pairRootMultiplicity, if_pos hpa]
    omega
  · have hpne : p ≠ 2 := fun he => hpa (he ▸ ha)
    simp only [pairRootMultiplicity, if_neg hpa]
    omega

lemma abs_card_pair_conditions_mixed (N a : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    |(((range N).filter (fun n => ∀ p ∈ P, p ∣ n*(a*n+1))).card : ℝ) -
      (N : ℝ)*(∏ p ∈ P, (pairRootMultiplicity a p : ℝ)/(p : ℝ))| ≤
        ∏ p ∈ P, (pairRootMultiplicity a p : ℝ) := by
  let d := ∏ p ∈ P, p
  have hd : 0 < d := prod_pos (fun p hp => (hP p hp).pos)
  have hh := abs_card_quadratic_divisibility N a d hd
  have hfilter : (range N).filter (fun n => d ∣ n*(a*n+1)) =
      (range N).filter (fun n => ∀ p ∈ P, p ∣ n*(a*n+1)) := by
    ext n
    simp only [mem_filter, d, prod_primes_dvd_iff P hP]
  have hroot : quadraticRootCount a d = ∏ p ∈ P, pairRootMultiplicity a p :=
    quadraticRootCount_product_mixed a P hP
  have hmain : (N : ℝ)/d * ((∏ p ∈ P, pairRootMultiplicity a p : ℕ) : ℝ) =
      (N : ℝ)*(∏ p ∈ P, (pairRootMultiplicity a p : ℝ)/(p : ℝ)) := by
    simp only [prod_div_distrib, d, Nat.cast_prod]
    ring
  rw [hfilter, hroot, hmain, Nat.cast_prod] at hh
  exact hh

lemma bounded_root_local_nonneg_le_six (p r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (hrp : r < p) :
    0 ≤ (r : ℝ)/(1-(r : ℝ)/(p : ℝ)) ∧
      (r : ℝ)/(1-(r : ℝ)/(p : ℝ)) ≤ 6 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hrR : (r : ℝ) < p := by exact_mod_cast hrp
  have hden : 0 < 1-(r : ℝ)/(p : ℝ) := sub_pos.mpr ((div_lt_one hp0).mpr hrR)
  refine ⟨div_nonneg (Nat.cast_nonneg r) hden.le, ?_⟩
  have hr : r = 1 ∨ r = 2 := by omega
  rcases hr with rfl | rfl
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hrp
    have hdiv : (1 : ℝ)/(p : ℝ) ≤ 1/2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
    norm_num only [Nat.cast_one] at hden ⊢
    apply (div_le_iff₀ hden).mpr
    linarith
  · have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hrp
    have hdiv : (2 : ℝ)/(p : ℝ) ≤ 2/3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    norm_num only [Nat.cast_ofNat] at hden ⊢
    apply (div_le_iff₀ hden).mpr
    linarith

lemma bounded_prime_product_sum_le_const_rpow (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ f : ℕ → ℝ, (∀ p ∈ P, 0 ≤ f p ∧ f p ≤ B) → ∀ z : ℕ, 0 < z →
        (∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z, ∏ p ∈ S, f p) ≤ C*(z : ℝ)^(1+ε) := by
  obtain ⟨C,hC,hbound⟩ := exists_card_pow_le_const_product_rpow B ε hB hε
  refine ⟨C,hC,?_⟩
  intro P hP f hf z hz
  let W := P.powerset.filter (fun S => (∏ p ∈ S, p) ≤ z)
  have hcard : (W.card : ℝ) ≤ z := by exact_mod_cast prime_product_sublevel_card_le P hP z
  have hterm (S : Finset ℕ) (hS : S ∈ W) : (∏ p ∈ S, f p) ≤ C*(z : ℝ)^ε := by
    have hSP := mem_powerset.mp (mem_filter.mp hS).1
    calc
      _ ≤ ∏ _p ∈ S, B := Finset.prod_le_prod (fun p hp => (hf p (hSP hp)).1)
        (fun p hp => (hf p (hSP hp)).2)
      _ = B^S.card := prod_const _
      _ ≤ C*(((∏ p ∈ S, p : ℕ) : ℝ)^ε) := hbound S (fun p hp => (hP p (hSP hp)).pos)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast (mem_filter.mp hS).2) hε.le) hC.le
  calc
    _ ≤ ∑ _S ∈ W, C*(z : ℝ)^ε := sum_le_sum hterm
    _ = (W.card : ℝ)*(C*(z : ℝ)^ε) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (z : ℝ)*(C*(z : ℝ)^ε) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [Real.rpow_add (by exact_mod_cast hz), Real.rpow_one]; ring

lemma eventually_bounded_prime_product_error (B δ : ℝ) (hB : 1 ≤ B) (hδ : 0 < δ) :
    ∀ᶠ z : ℕ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      ∀ f : ℕ → ℝ, (∀ p ∈ P, 0 ≤ f p ∧ f p ≤ B) →
        (∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z, ∏ p ∈ S, f p)^2 ≤ (z : ℝ)^(2+δ) := by
  obtain ⟨C,hC,hbound⟩ := bounded_prime_product_sum_le_const_rpow B (δ/4) hB (by linarith)
  have ht : Tendsto (fun z : ℕ => (z : ℝ)^(δ/2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < δ/2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (C^2)), eventually_ge_atTop 1]
    with z hzC hz
  intro P hP f hf
  have hz0 : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hnonneg : 0 ≤ ∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z, ∏ p ∈ S, f p := by
    apply sum_nonneg
    intro S hS
    exact prod_nonneg (fun p hp => (hf p (mem_powerset.mp (mem_filter.mp hS).1 hp)).1)
  calc
    _ ≤ (C*(z : ℝ)^(1+δ/4))^2 := pow_le_pow_left₀ hnonneg (hbound P hP f hf z (by omega)) 2
    _ = C^2*(z : ℝ)^(2+δ/2) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hz0.le]
      congr 2
      norm_num
      ring
    _ ≤ (z : ℝ)^(δ/2)*(z : ℝ)^(2+δ/2) :=
      mul_le_mul_of_nonneg_right hzC (Real.rpow_nonneg hz0.le _)
    _ = _ := by rw [← Real.rpow_add hz0]; congr 1; ring

noncomputable def mixedPairDenominator (a z : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ S ∈ P.powerset with (∏ p ∈ S, p) ≤ z,
    (∏ p ∈ S, (((pairRootMultiplicity a p : ℝ)/(p : ℝ))⁻¹-1))⁻¹

/-- The same quadratic-scale error is available with the true local roots. -/
theorem eventually_mixed_prime_pair_sieve_bound (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ z : ℕ in atTop, ∀ N a : ℕ, 2 ∣ a → ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime ∧ p ≤ z) →
        (((range N).filter (fun q => q.Prime ∧ (a*q+1).Prime ∧ z<q ∧ z<a*q+1)).card : ℝ) ≤
          (N : ℝ)*(mixedPairDenominator a z P)⁻¹+(z : ℝ)^(2+δ) := by
  filter_upwards [eventually_bounded_prime_product_error 6 δ (by norm_num) hδ,
    eventually_ge_atTop 1] with z hz hz1
  intro N a ha P hP
  let ρ : ℕ → ℝ := fun p => (pairRootMultiplicity a p : ℝ)
  let bad : ℕ → ℕ → Prop := fun p q => p ∣ q*(a*q+1)
  have hρ : ∀ p ∈ P, 1 ≤ ρ p ∧ ρ p < p := by
    intro p hp
    have hh := pairRootMultiplicity_properties a p ha (hP p hp).1
    change (1 : ℝ) ≤ (pairRootMultiplicity a p : ℝ) ∧ (pairRootMultiplicity a p : ℝ) < p
    exact ⟨by exact_mod_cast hh.1, by exact_mod_cast hh.2.2⟩
  have hcount : ∀ S ∈ P.powerset,
      |(((range N).filter (fun q => ∀ p ∈ S, bad p q)).card : ℝ) -
        (N : ℝ)*(∏ p ∈ S, ρ p/p)| ≤ ∏ p ∈ S, ρ p := by
    intro S hS
    convert abs_card_pair_conditions_mixed N a S
      (fun p hp => (hP p (mem_powerset.mp hS hp)).1) using 1
    congr 3
    congr 1
    ext q
    simp only [mem_filter, bad]
  have hb := finite_selberg_bound_local (range N) P (fun p hp => (hP p hp).1)
    bad ρ hρ (N : ℝ) z hz1 hcount
  have herr := hz P (fun p hp => (hP p hp).1)
    (fun p => ρ p/(1-ρ p/p)) (by
      intro p hp
      have hh := pairRootMultiplicity_properties a p ha (hP p hp).1
      exact bounded_root_local_nonneg_le_six p _ hh.1 hh.2.1 hh.2.2)
  apply le_trans ?_ (hb.trans (add_le_add le_rfl herr))
  apply Nat.cast_le.mpr
  apply card_le_card
  intro q hq
  obtain ⟨hqN,hqp,haqp,hzq,hzaq⟩ := mem_filter.mp hq
  refine mem_filter.mpr ⟨hqN,?_⟩
  intro p hp hbad
  rcases (hP p hp).1.dvd_mul.mp hbad with hdiv | hdiv
  · have he := (Nat.prime_dvd_prime_iff_eq (hP p hp).1 hqp).mp hdiv
    have := (hP p hp).2
    omega
  · have he := (Nat.prime_dvd_prime_iff_eq (hP p hp).1 haqp).mp hdiv
    have := (hP p hp).2
    omega

end Erdos821.Sieve
