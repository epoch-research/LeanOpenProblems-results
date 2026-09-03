import Submission.WeightedCofactorPairs
import Submission.PrimeSmoothNeighborRuns

/-! A cofactor-dependent endpoint saves one logarithm when the smaller
prime label lies in a fixed multiplicative band. No signed estimate for
the power-cofactor interior is asserted. -/
namespace Erdos371
open Finset Filter FiniteSieve DilationSpectrum
open scoped Topology

noncomputable def narrowLoserCofactorSet (X H z : ℕ) : Finset ℕ :=
  (Icc 1 H).biUnion fun a => (Icc 1 H).biUnion fun b =>
    cofactorPrimePairSet (2*X*max a b) a b z

lemma narrowLoserCofactorSet_bound (X H z : ℕ) (hX : 0 < X)
    (hH : H ≤ X) (hz : 1 ≤ z) :
    ((narrowLoserCofactorSet X H z).card : ℝ) ≤
      16*Real.exp 19*X*H*(1+Real.log H)/(Real.log (z+1 : ℝ))^2 +
        2*(H : ℝ)^2*(z+1 : ℝ)^64 := by
  have hc : (narrowLoserCofactorSet X H z).card ≤
      ∑ a ∈ Icc 1 H, ∑ b ∈ Icc 1 H,
        (cofactorPrimePairSet (2*X*max a b) a b z).card :=
    card_biUnion_le.trans (sum_le_sum fun _ _ => card_biUnion_le)
  have hcr := (Nat.cast_le (α := ℝ)).mpr hc
  simp only [Nat.cast_sum] at hcr
  let C : ℝ := 8*Real.exp 3*X/(Real.log (z+1 : ℝ))^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrow (a b : ℕ) (ha : a ∈ Icc 1 H) (hb : b ∈ Icc 1 H) :
      ((cofactorPrimePairSet (2*X*max a b) a b z).card : ℝ) ≤
        C*((max a b : ℕ)*slopeSieveFactor (a*b)/((a : ℝ)*b)) +
          2*(z+1 : ℝ)^64 := by
    obtain ⟨ha1,haH⟩ := mem_Icc.mp ha
    obtain ⟨hb1,hbH⟩ := mem_Icc.mp hb
    have hprod : a*b ≤ 2*X*max a b := by
      have hh := Nat.mul_le_mul (haH.trans hH) (le_max_right a b)
      nlinarith
    have h := cofactorPrimePairSet_selberg_bound_of_product_le
      (2*X*max a b) a b z ha1 hb1 hz hprod
    apply h.trans_eq
    dsimp only [C]
    push_cast
    ring
  have hsum := sum_le_sum (s := Icc 1 H) fun a ha =>
    sum_le_sum (s := Icc 1 H) fun b hb => hrow a b ha hb
  have he : (∑ a ∈ Icc 1 H, ∑ b ∈ Icc 1 H,
      (C*((max a b : ℕ)*slopeSieveFactor (a*b)/((a : ℝ)*b)) +
        2*(z+1 : ℝ)^64)) =
      C*(∑ a ∈ Icc 1 H, ∑ b ∈ Icc 1 H,
        (max a b : ℕ)*slopeSieveFactor (a*b)/((a : ℝ)*b)) +
          2*(H : ℝ)^2*(z+1 : ℝ)^64 := by
    simp only [sum_add_distrib,← mul_sum,sum_const,Nat.card_Icc,
      Nat.add_sub_cancel,nsmul_eq_mul]
    ring
  rw [he] at hsum
  have hm := mul_le_mul_of_nonneg_left (weightedSlopeSum_bound H) hC
  have h19 : Real.exp 19 = Real.exp 3*Real.exp 16 := by
    rw [← Real.exp_add]
    norm_num
  apply (hcr.trans hsum).trans
  apply add_le_add _ le_rfl
  apply hm.trans_eq
  dsimp only [C]
  rw [h19]
  ring

def narrowLoserSet (X N : ℕ) : Finset ℕ :=
  (bothAboveSet X N).filter fun n => primeLoser n ≤ 2*X

lemma narrowLoserSet_subset_cofactors (X H z : ℕ) (hX : 0 < X) (hz : z ≤ X) :
    narrowLoserSet X (H*X) ⊆ narrowLoserCofactorSet X H z := by
  intro n hn
  obtain ⟨hnboth,hnmin⟩ := mem_filter.mp hn
  obtain ⟨hnrange,hnP,hnP'⟩ := mem_filter.mp hnboth
  have hnN := mem_range.mp hnrange
  have hn2 : 1 < n := by
    apply (Nat.one_lt_maxPrimeFac_iff n).mp
    omega
  obtain ⟨ha0,had,hpa⟩ := primeCofactor_data n hn2
  obtain ⟨hb0,hbd,hqb⟩ := primeCofactor_data (n+1) (by omega)
  let a := primeCofactor n
  let b := primeCofactor (n+1)
  have hea : Nat.maxPrimeFac n*a = n := maxPrimeFac_mul_primeCofactor n
  have heb : Nat.maxPrimeFac (n+1)*b = n+1 := maxPrimeFac_mul_primeCofactor (n+1)
  have haH : a ≤ H := by
    have h := Nat.mul_le_mul_right a hnP.le
    rw [hea] at h
    nlinarith
  have hbH : b ≤ H := by
    have h := Nat.mul_le_mul_right b hnP'.le
    rw [heb] at h
    nlinarith
  have hend : n ≤ 2*X*max a b := by
    simp only [primeLoser,min_le_iff] at hnmin
    rcases hnmin with hl | hr
    · have h := Nat.mul_le_mul hl (le_max_left a b)
      rw [hea] at h
      exact h
    · have h := Nat.mul_le_mul hr (le_max_right a b)
      rw [heb] at h
      omega
  apply mem_biUnion.mpr
  refine ⟨a,mem_Icc.mpr ⟨ha0,haH⟩,?_⟩
  apply mem_biUnion.mpr
  refine ⟨b,mem_Icc.mpr ⟨hb0,hbH⟩,?_⟩
  apply mem_filter.mpr
  refine ⟨mem_Icc.mpr ⟨by omega,hend⟩,had,hbd,?_⟩
  rw [hpa,hqb]
  exact ⟨Nat.prime_maxPrimeFac_of_one_lt n hn2,
    Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega),hz.trans_lt hnP,hz.trans_lt hnP'⟩

lemma narrowLoserSet_card_bound (X H z : ℕ) (hX : 0 < X)
    (hH : H ≤ X) (hz1 : 1 ≤ z) (hz : z ≤ X) :
    ((narrowLoserSet X (H*X)).card : ℝ) ≤
      16*Real.exp 19*X*H*(1+Real.log H)/(Real.log (z+1 : ℝ))^2 +
        2*(H : ℝ)^2*(z+1 : ℝ)^64 :=
  ((Nat.cast_le (α := ℝ)).mpr (card_le_card (narrowLoserSet_subset_cofactors X H z hX hz))).trans
    (narrowLoserCofactorSet_bound X H z hX hH hz1)

lemma roughNeighborPrimes_subset_narrowLoser_image (K X : ℕ) (hX : 0 < X) (hK : K ≤ X) :
    roughNeighborPrimes K X ⊆ (narrowLoserSet X ((2*K+1)*X)).image primeLoser := by
  intro p hp
  have hband := (mem_filter.mp hp).1
  obtain ⟨_,_,hpupper⟩ := dyadicPrimeBand_nat_data hband
  obtain ⟨n,hn,hlabel⟩ := mem_image.mp (roughNeighborPrimes_subset_loser_image K X hX hK hp)
  exact mem_image.mpr ⟨n,mem_filter.mpr ⟨hn,by rwa [hlabel]⟩,hlabel⟩

lemma roughNeighborPrimes_card_le_narrowLoser (K X : ℕ) (hX : 0 < X) (hK : K ≤ X) :
    (roughNeighborPrimes K X).card ≤ (narrowLoserSet X ((2*K+1)*X)).card :=
  (card_le_card (roughNeighborPrimes_subset_narrowLoser_image K X hX hK)).trans card_image_le

noncomputable def narrowLoserSieveConstant : ℝ := 16*Real.exp 19*128^2

/-- The cofactor-dependent endpoint yields a single log H rather than a
squared log H in the main term. -/
theorem narrowLoserSet_scaled_log_bound (X H : ℕ) (hX : 1 < X) (hH : H ≤ X) :
    ((narrowLoserSet X (H*X)).card : ℝ)*Real.log X/X ≤
      narrowLoserSieveConstant*H*(1+Real.log H)/Real.log X +
        (2 : ℝ)^65*(H : ℝ)^2*Real.log X/(X : ℝ)^(1/2 : ℝ) := by
  let z := ⌊(X : ℝ)^(1/128 : ℝ)⌋₊
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX.le
  have hlogX : 0 < Real.log X := Real.log_pos (by exact_mod_cast hX)
  have hz1 : 1 ≤ z := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hX1 (by norm_num))
  have hzX : z ≤ X := by
    have h := (Nat.floor_le (Real.rpow_nonneg hX0.le (1/128 : ℝ))).trans
      (show (X : ℝ)^(1/128 : ℝ) ≤ X from by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num : (1/128 : ℝ) ≤ 1))
    exact_mod_cast h
  have hzupper : (z+1 : ℝ) ≤ 2*(X : ℝ)^(1/128 : ℝ) := by
    have hz := Nat.floor_le (Real.rpow_nonneg hX0.le (1/128 : ℝ))
    have hpow := Real.one_le_rpow hX1 (by norm_num : (0 : ℝ) ≤ 1/128)
    dsimp only [z]
    linarith
  have hlogz : Real.log X/128 ≤ Real.log (z+1 : ℝ) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hX0 (1/128 : ℝ))
      (Nat.lt_floor_add_one ((X : ℝ)^(1/128 : ℝ))).le
    rw [Real.log_rpow hX0] at h
    convert h using 1
    ring
  have hlogz0 : 0 < Real.log (z+1 : ℝ) := lt_of_lt_of_le (by positivity) hlogz
  have hzpow : (z+1 : ℝ)^64 ≤ (2 : ℝ)^64*(X : ℝ)^(1/2 : ℝ) := by
    calc
      _ ≤ (2*(X : ℝ)^(1/128 : ℝ))^64 := pow_le_pow_left₀ (by positivity) hzupper 64
      _ = _ := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast,← Real.rpow_mul hX0.le]
        norm_num
  have hb := mul_le_mul_of_nonneg_right (narrowLoserSet_card_bound X H z (by omega) hH hz1 hzX)
    (div_nonneg hlogX.le hX0.le)
  have hmain : 16*Real.exp 19*X*H*(1+Real.log H)/(Real.log (z+1 : ℝ))^2*
      (Real.log X/X) ≤ narrowLoserSieveConstant*H*(1+Real.log H)/Real.log X := by
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ Real.log X/128) hlogz 2
    have hc : 0 ≤ 16*Real.exp 19*X*H*(1+Real.log H) := by
      have := Real.log_natCast_nonneg H
      positivity
    have hh := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left hc (by positivity : 0 < (Real.log X/128)^2) hsq)
      (div_nonneg hlogX.le hX0.le)
    apply hh.trans_eq
    unfold narrowLoserSieveConstant
    field_simp
  have hpoweq : (X : ℝ)^(1/2 : ℝ)/X = 1/(X : ℝ)^(1/2 : ℝ) := by
    calc
      _ = (X : ℝ)^(1/2 : ℝ)/(X : ℝ)^(1 : ℝ) := by rw [Real.rpow_one]
      _ = (X : ℝ)^(-(1/2 : ℝ)) := by rw [← Real.rpow_sub hX0]; norm_num
      _ = _ := by rw [Real.rpow_neg hX0.le]; simp only [one_div]
  have herr : 2*(H : ℝ)^2*(z+1 : ℝ)^64*(Real.log X/X) ≤
      (2 : ℝ)^65*(H : ℝ)^2*Real.log X/(X : ℝ)^(1/2 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hzpow (show 0 ≤ 2*(H : ℝ)^2 by positivity))
      (div_nonneg hlogX.le hX0.le)
    apply hh.trans_eq
    calc
      _ = (2 : ℝ)^65*(H : ℝ)^2*Real.log X*((X : ℝ)^(1/2 : ℝ)/X) := by ring
      _ = _ := by rw [hpoweq]; ring
  calc
    _ ≤ _ := by simpa only [mul_div_assoc] using hb
    _ = _ := add_mul _ _ _
    _ ≤ _ := add_le_add hmain herr

#print axioms narrowLoserCofactorSet_bound
#print axioms narrowLoserSet_subset_cofactors
#print axioms roughNeighborPrimes_card_le_narrowLoser
#print axioms narrowLoserSet_scaled_log_bound
end Erdos371
