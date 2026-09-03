import Submission.LongCofactorHyperbolicBound
import Submission.MixedCompositeSieve

/-!
# The short-cofactor tail via the existing mixed-root pair sieve

The long-cofactor argument need not cover the extreme top end of the prime
variable. Its complement is charged through the reciprocal-totient average
of the remaining small cofactors.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 4000000

lemma hyperbolic_prime_pair_card_le_cofactor_sum (c H Y Z A : ℕ)
    (hc : 0 < c) (hY : 0 < Y) (hA : H/Y ≤ A) :
    (hyperbolicPrimePairPool c H Y Z).card ≤
      ∑ a ∈ Icc 1 A, primePairCofactorCount (c*H) (c*a) := by
  classical
  let P (a : ℕ) := (range (c*H/(c*a)+1)).filter
    (fun q => q.Prime ∧ ((c*a)*q+1).Prime)
  let T (a : ℕ) := (P a).image (fun q => (a,q))
  have hsub : hyperbolicPrimePairPool c H Y Z ⊆ (Icc 1 A).biUnion T := by
    intro x hx
    obtain ⟨hxI,hprod,hprime,hsucc⟩ := mem_filter.mp hx
    obtain ⟨hxa,hxn⟩ := mem_product.mp hxI
    have ha0 : 0 < x.1 := (mem_Icc.mp hxa).1
    have hnY : Y ≤ x.2 := Nat.le_of_succ_le (mem_Icc.mp hxn).1
    have haA : x.1 ≤ A :=
      ((Nat.le_div_iff_mul_le hprime.pos).mpr hprod).trans
        ((Nat.div_le_div_left hnY hY).trans hA)
    have hqN : x.2 ≤ c*H/(c*x.1) := by
      apply (Nat.le_div_iff_mul_le (Nat.mul_pos hc ha0)).mpr
      have hh := Nat.mul_le_mul_left c hprod
      convert hh using 1; ring
    refine mem_biUnion.mpr ⟨x.1,mem_Icc.mpr ⟨ha0,haA⟩,?_⟩
    exact mem_image.mpr ⟨x.2,mem_filter.mpr ⟨mem_range.mpr (by omega),hprime,hsucc⟩,rfl⟩
  apply ((card_le_card hsub).trans card_biUnion_le).trans_eq
  apply sum_congr rfl
  intro a ha
  rw [show (T a).card=(P a).card from card_image_of_injective _ (by intro q r h; exact congrArg Prod.snd h)]
  rfl

/-- A finite tail estimate; the logarithmic factor comes from the short
cofactor cutoff A, not from the full prime-variable range. -/
lemma hyperbolic_short_cofactor_bound (c H Y Z A J : ℕ)
    (hc : 0 < c) (hY : 0 < Y) (hA : H/Y ≤ A) (hAH : A ≤ H)
    (hJ : 0 < J) (hmixed : MixedPairAt J) :
    ((hyperbolicPrimePairPool c H Y Z).card : ℝ) ≤
      ((1/75 : ℝ)*(H : ℝ)*((c : ℝ)/(c.totient : ℝ))*(harmonic A : ℝ)/((J : ℝ)*Real.log 2)^2)+
        (A : ℝ)*((2 : ℝ)^(64*J)+(2 : ℝ)^(16*J)+1) := by
  have hcount := Nat.cast_le (α := ℝ).mpr
    (hyperbolic_prime_pair_card_le_cofactor_sum c H Y Z A hc hY hA)
  rw [Nat.cast_sum] at hcount
  have hsum := sum_prime_pair_composite_cofactor_mixed (c*H) A J c hc
    (Nat.mul_le_mul_left c hAH) hJ hmixed
  apply (hcount.trans hsum).trans_eq
  push_cast
  ring

lemma dyadic_tail_cofactor_bound (h u m : ℕ) (hu : u ≤ h) (H : ℕ)
    (hH : H ≤ 2^(128*h*m)) :
    H/2^(128*u*m) ≤ 2^(128*(h-u)*m) := by
  apply (Nat.div_le_div_right hH).trans_eq
  have he : 128*h*m = 128*(h-u)*m+128*u*m := by
    nlinarith only [Nat.sub_add_cancel hu]
  rw [he,pow_add,Nat.mul_div_cancel _ (by positivity : 0<2^(128*u*m))]

/-- An explicit power-grid version of the short tail, uniform in H and c.
The contribution proportional to h-u vanishes as that ratio shrinks. -/
theorem eventually_short_cofactor_dyadic_bound (h u : ℕ) (hu : 1 ≤ u) (huh : u ≤ h) :
    ∀ᶠ m : ℕ in atTop, ∀ c H Z : ℕ, 0 < c → H ≤ 2^(128*h*m) →
      ((hyperbolicPrimePairPool c H (2^(128*u*m)) Z).card : ℝ) ≤
        ((1/75 : ℝ)*(H : ℝ)*((c : ℝ)/(c.totient : ℝ))*
          (1+128*((h-u : ℕ) : ℝ)*m*Real.log 2)/(((u*m : ℕ) : ℝ)*Real.log 2)^2)+
            (2 : ℝ)^(128*(h-u)*m)*((2 : ℝ)^(64*u*m)+(2 : ℝ)^(16*u*m)+1) := by
  have hmixed : ∀ᶠ m : ℕ in atTop, MixedPairAt (u*m) := by
    obtain ⟨J,hJ⟩ := eventually_atTop.mp eventually_mixed_pair_at
    filter_upwards [eventually_ge_atTop J] with m hm
    exact hJ (u*m) (hm.trans (Nat.le_mul_of_pos_left m hu))
  filter_upwards [hmixed,eventually_ge_atTop 1] with m hm hm1
  intro c H Z hc hH
  let A := H/2^(128*u*m)
  have hA : A ≤ 2^(128*(h-u)*m) := dyadic_tail_cofactor_bound h u m huh H hH
  have hsum := hyperbolic_short_cofactor_bound c H (2^(128*u*m)) Z A (u*m) hc
    (by positivity) le_rfl (Nat.div_le_self _ _) (Nat.mul_pos hu hm1) hm
  have hHarm : (harmonic A : ℝ) ≤ 1+128*((h-u : ℕ) : ℝ)*m*Real.log 2 := by
    have hh := harmonic_le_one_add_log A
    have hlog := log_nat_mono hA
    rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at hlog
    push_cast at hlog
    linarith only [hh,hlog]
  apply hsum.trans
  have hmain := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hHarm (show 0 ≤ (1/75 : ℝ)*(H : ℝ)*((c : ℝ)/(c.totient : ℝ)) by positivity))
    (sq_nonneg (((u*m : ℕ) : ℝ)*Real.log 2))
  have herr := mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ).mpr hA)
    (show 0 ≤ (2 : ℝ)^(64*(u*m))+(2 : ℝ)^(16*(u*m))+1 by positivity)
  convert _root_.add_le_add hmain herr using 1; simp only [Nat.cast_pow,Nat.cast_ofNat,mul_assoc]

end Erdos821.AnalyticSieve
