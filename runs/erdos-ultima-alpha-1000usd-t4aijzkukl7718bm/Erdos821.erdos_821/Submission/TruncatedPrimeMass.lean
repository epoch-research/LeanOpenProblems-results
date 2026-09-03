import Submission.PrimeMassLogBounds

/-!
# Selecting a bounded-size prime product with large reciprocal mass

A first-moment truncation of a finite Euler product avoids a geometric
loss in the divisor order. The cutoff depends on the prime scale.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma half_euler_product_card_truncated (P : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (R : ℕ) (hR : 1 ≤ R)
    (hmass : 2*(∑ p ∈ P, w p) ≤ R) :
    (∏ p ∈ P, (1+w p))/2 ≤ ∑ S ∈ P.powerset.filter (fun S => S.card ≤ R), ∏ p ∈ S, w p := by
  let F := ∏ p ∈ P, (1+w p)
  let B := P.powerset.filter (fun S => ¬S.card ≤ R)
  have hF : 0 ≤ F := prod_nonneg (fun p hp => by linarith [hw p hp])
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hweight (S : Finset ℕ) (hS : S ∈ P.powerset) : 0 ≤ ∏ p ∈ S, w p :=
    prod_nonneg (fun p hp => hw p (mem_powerset.mp hS hp))
  have hmean := Sieve.powerset_weighted_sum_moment P w (fun _ => 1)
    (fun p hp => by have := hw p hp; positivity)
  simp only [sum_const,nsmul_eq_mul,mul_one] at hmean
  have hmeanle : (∑ S ∈ P.powerset, (∏ p ∈ S, w p)*(S.card : ℝ)) ≤
      F*(∑ p ∈ P, w p) := by
    rw [hmean]
    apply mul_le_mul_of_nonneg_left _ hF
    apply sum_le_sum
    intro p hp
    exact div_le_self (hw p hp) (by linarith [hw p hp])
  have htail : (R : ℝ)*(∑ S ∈ B, ∏ p ∈ S, w p) ≤ F*(∑ p ∈ P, w p) := by
    calc
      _ = ∑ S ∈ B, (∏ p ∈ S, w p)*(R : ℝ) := by rw [mul_sum]; apply sum_congr rfl; intros; ring
      _ ≤ ∑ S ∈ B, (∏ p ∈ S, w p)*(S.card : ℝ) := by
        apply sum_le_sum
        intro S hS
        obtain ⟨hSP,hSR⟩ := mem_filter.mp hS
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show R ≤ S.card by omega)) (hweight S hSP)
      _ ≤ ∑ S ∈ P.powerset, (∏ p ∈ S, w p)*(S.card : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun S hS _ => mul_nonneg (hweight S hS) (Nat.cast_nonneg _))
      _ ≤ _ := hmeanle
  have htotal := sum_filter_add_sum_filter_not P.powerset (fun S => S.card ≤ R)
    (fun S => ∏ p ∈ S, w p)
  rw [← prod_one_add] at htotal
  change (∑ S ∈ P.powerset.filter (fun S => S.card ≤ R), ∏ p ∈ S, w p)+
    (∑ S ∈ B, ∏ p ∈ S, w p) = F at htotal
  have h := mul_le_mul_of_nonneg_left hmass hF
  change F/2 ≤ _
  nlinarith only [htail,htotal,h,hR0]

lemma card_truncated_mass_eq_sum (P : Finset ℕ) (w : ℕ → ℝ) (a : ℝ) (R : ℕ) :
    (∑ S ∈ P.powerset.filter (fun S => S.card ≤ R), ∏ p ∈ S, (a*w p)) =
      ∑ r ∈ range (R+1), a^r*elementaryMass P w r := by
  let T := P.powerset.filter (fun S => S.card ≤ R)
  have hmap : ∀ S ∈ T, S.card ∈ range (R+1) := by
    intro S hS
    exact mem_range.mpr (by have := (mem_filter.mp hS).2; omega)
  rw [← sum_fiberwise_of_maps_to hmap (fun S => ∏ p ∈ S, (a*w p))]
  apply sum_congr rfl
  intro r hr
  have he : T.filter (fun S => S.card=r) = P.powersetCard r := by
    ext S
    simp only [T,mem_filter,mem_powerset,mem_powersetCard]
    have hrR : r ≤ R := by have := mem_range.mp hr; omega
    constructor
    · exact fun h => ⟨h.1.1,h.2⟩
    · rintro ⟨hSP,hcard⟩
      exact ⟨⟨hSP,by omega⟩,hcard⟩
  rw [he]
  unfold elementaryMass
  rw [mul_sum]
  apply sum_congr rfl
  intro S hS
  rw [prod_mul_distrib,prod_const,(mem_powersetCard.mp hS).2]

lemma exists_large_primeSubset_mass (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (a : ℝ) (ha : 0 ≤ a) (R : ℕ) (hR : 1 ≤ R)
    (hmass : 2*a*poolTotientMass P ≤ R) :
    ∃ r ≤ R, (∏ p ∈ P, (1+a*(p.totient : ℝ)⁻¹))/(2*((R : ℝ)+1)) ≤
      a^r*poolTotientMass (primeSubsetModuli P r) := by
  have h := half_euler_product_card_truncated P (fun p => a*(p.totient : ℝ)⁻¹)
    (fun p _ => mul_nonneg ha (inv_nonneg.mpr (Nat.cast_nonneg _))) R hR (by
      simpa only [← mul_sum,mul_assoc,poolTotientMass] using hmass)
  rw [card_truncated_mass_eq_sum] at h
  have hsum : (∑ _r ∈ range (R+1), (∏ p ∈ P, (1+a*(p.totient : ℝ)⁻¹))/(2*((R : ℝ)+1))) ≤
      ∑ r ∈ range (R+1), a^r*elementaryMass P (fun p => (p.totient : ℝ)⁻¹) r := by
    apply le_trans (le_of_eq ?_) h
    rw [sum_const,nsmul_eq_mul,card_range,Nat.cast_add,Nat.cast_one]
    field_simp
  obtain ⟨r,hr,hrmass⟩ := exists_le_of_sum_le (show (range (R+1)).Nonempty from
    ⟨0,mem_range.mpr (by omega)⟩) hsum
  refine ⟨r,by have := mem_range.mp hr; omega,?_⟩
  simpa only [primeSubsetModuli_mass P hP] using hrmass

lemma log_one_add_small_lower (A x : ℝ) (hA : 0 < A) (hx : 0 ≤ x) (hAx : A*x ≤ 1) :
    (A/(A+1))*x ≤ Real.log (1+x) := by
  have hpos : 0 < 1+x := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have he : 1-(1+x)⁻¹ = (1/(1+x))*x := by field_simp; ring
  rw [he] at hlog
  apply le_trans _ hlog
  apply mul_le_mul_of_nonneg_right _ hx
  apply (div_le_div_iff₀ (by positivity : 0 < A+1) hpos).mpr
  nlinarith only [hAx]

lemma powerPrimePool_euler_lower (w A E : ℕ) (hw : 1 ≤ w) (hA : 10 ≤ A)
    (hE : 1 ≤ E) (hlogE : 1024 ≤ Real.log E)
    (hL : 2*w*A ≤ progressionScaleN E) :
    (E : ℝ)^(w*(A-10)) ≤ ∏ p ∈ powerPrimePool A E, (1+(w : ℝ)*(p.totient : ℝ)⁻¹) := by
  let P := powerPrimePool A E
  let c : ℝ := (A : ℝ)/((A : ℝ)+1)
  have hAR : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hER : (0 : ℝ) < E := by exact_mod_cast hE
  have hL0 : (0 : ℝ) < progressionScaleN E := by unfold progressionScaleN; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hlogs : c*(w : ℝ)*poolTotientMass P ≤
      ∑ p ∈ P, Real.log (1+(w : ℝ)*(p.totient : ℝ)⁻¹) := by
    unfold poolTotientMass
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hpb := powerPrimePool_prime_bounds A E p hp
    have hinv := prime_reciprocal_totient_le_twice_inv _ p (by unfold progressionScaleN; positivity)
      hpb.1 hpb.2.1
    have hsmall : (A : ℝ)*((w : ℝ)*(p.totient : ℝ)⁻¹) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hinv (show 0 ≤ (A : ℝ)*(w : ℝ) by positivity)
      have hL' : (2 : ℝ)*(w : ℝ)*(A : ℝ) ≤ progressionScaleN E := by exact_mod_cast hL
      have hb : (A : ℝ)*(w : ℝ)*(2/(progressionScaleN E : ℝ)) ≤ 1 := by
        apply (le_of_mul_le_mul_right ?_ hL0)
        rw [mul_assoc,div_mul_cancel₀ _ hL0.ne',one_mul]
        nlinarith only [hL']
      nlinarith only [h,hb]
    have h := log_one_add_small_lower (A : ℝ) ((w : ℝ)*(p.totient : ℝ)⁻¹) hAR (by positivity) hsmall
    simpa only [c,mul_assoc] using h
  have hmass : ((A : ℝ)-9)*Real.log E ≤ poolTotientMass P := by
    have h := powerPrimePool_mass_lower A E hE
    change _ ≤ poolTotientMass P at h
    nlinarith only [h,hlogE]
  have hcoef : (A : ℝ)-10 ≤ c*((A : ℝ)-9) := by
    dsimp [c]
    apply (le_of_mul_le_mul_right ?_ (show 0 < (A : ℝ)+1 by positivity))
    field_simp
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hmass (show 0 ≤ c*(w : ℝ) by positivity)
  have hmul' := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ (w : ℝ)*Real.log E by positivity)
  have hlow : ((w*(A-10) : ℕ) : ℝ)*Real.log E ≤
      ∑ p ∈ P, Real.log (1+(w : ℝ)*(p.totient : ℝ)⁻¹) := by
    rw [Nat.cast_mul,Nat.cast_sub (by omega : 10 ≤ A),Nat.cast_ofNat]
    nlinarith only [hlogs,hmul,hmul']
  have h := Real.exp_le_exp.mpr hlow
  rw [Real.exp_sum] at h
  have he : Real.exp (((w*(A-10) : ℕ) : ℝ)*Real.log E) = (E : ℝ)^(w*(A-10)) := by
    rw [Real.exp_nat_mul,Real.exp_log hER]
  rw [he] at h
  convert h using 1
  apply prod_congr rfl
  intro p hp
  rw [Real.exp_log (by positivity)]

end Erdos821
