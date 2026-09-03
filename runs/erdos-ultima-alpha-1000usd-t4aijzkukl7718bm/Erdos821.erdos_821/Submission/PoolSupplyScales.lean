import Submission.PoolNarrowHyperbolas
import Submission.ScaledProductRoughBound

/-!
# Concrete retained-pool supply scales

The narrow multiplier blocks preserve full-product length at the top
prime cutoff. Floor losses are handled before comparing power scales.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821.AnalyticSieve
set_option maxHeartbeats 5000000

lemma cofactorScale_double_index_eq (s m : ℕ) : cofactorScale s (2*m) = 2^(512*s*m) := by
  rw [cofactorScale_eq]
  congr 1
  ring

lemma multiplier_floor_half (X C D Q : ℕ) (hC : 0 < C) (hQ : 0 < Q)
    (hCD : C ≤ D) (hX : C*Q ≤ X) : X/(2*Q) ≤ D*(X/C/Q) := by
  let F := X/(C*Q)
  have hF : 1 ≤ F := Nat.div_pos hX (Nat.mul_pos hC hQ)
  have hlt := Nat.lt_mul_div_succ X (Nat.mul_pos hC hQ)
  change X < C*Q*(F+1) at hlt
  have hh : X ≤ 2*Q*(C*F) := by nlinarith only [hlt,mul_le_mul_of_nonneg_left (show F+1 ≤ 2*F by omega) (Nat.zero_le (C*Q))]
  calc
    X/(2*Q) ≤ (2*Q*(C*F))/(2*Q) := Nat.div_le_div_right hh
    _ = C*F := Nat.mul_div_right _ (by omega)
    _ ≤ D*F := Nat.mul_le_mul_right F hCD
    _ = _ := by rw [Nat.div_div_eq_div_mul]

lemma multiplier_floor_upper (X C D Q : ℕ) (hQ : 0 < Q) (hDC : D ≤ 2*C) :
    D*(X/C/Q) ≤ 2*(X/Q) := by
  rw [Nat.div_div_eq_div_mul]
  have hprod : C*(X/(C*Q)) ≤ X/Q := by
    apply (Nat.le_div_iff_mul_le hQ).mpr
    have hh := Nat.div_mul_le_self X (C*Q)
    nlinarith only [hh]
  calc
    _ ≤ 2*C*(X/(C*Q)) := Nat.mul_le_mul_right (X/(C*Q)) hDC
    _ = 2*(C*(X/(C*Q))) := by ring
    _ ≤ _ := Nat.mul_le_mul_left 2 hprod

lemma multiplierUpper_le_two_lower (k r j : ℕ) : multiplierUpper k r j ≤ 2*multiplierLower k r j := by
  have h : 1 ≤ (2 : ℕ)^r := Nat.one_le_pow _ _ (by decide)
  unfold multiplierLower multiplierUpper
  nlinarith only [Nat.mul_le_mul_right (2^(k-r)) (show 2^r+j+1 ≤ 2*(2^r+j) by omega)]

lemma pool_supply_short_prefix (m X C : ℕ) (hm : 1000000 ≤ m)
    (hX : independentN 40000020 m ≤ X) (hC : 0 < C)
    (hCup : C ≤ 2^(64*20000004*m+1)) :
    cofactorScale 3 (2*cofactorDyadicIndex 100000000 (64*20000014*m)) ≤
      (X/C)/2^(64*20000014*m) := by
  have hh := (cofactorDyadicIndex_bounds 100000000 (64*20000014*m) (by decide)).2
  have hexp : 512*3*cofactorDyadicIndex 100000000 (64*20000014*m)+
      64*20000014*m+(64*20000004*m+1) ≤ 64*40000020*m := by nlinarith only [hh,hm]
  rw [cofactorScale_double_index_eq]
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2^(64*20000014*m))).mpr
  apply (Nat.le_div_iff_mul_le hC).mpr
  apply le_trans (Nat.mul_le_mul_left _ hCup)
  apply le_trans _ hX
  unfold independentN
  rw [← pow_add,← pow_add]
  exact Nat.pow_le_pow_right (by decide) hexp

lemma pool_supply_product_lower (m X C D : ℕ) (hm : 1000000 ≤ m)
    (hX : independentN 40000020 m ≤ X) (hC : 0 < C) (hCD : C ≤ D)
    (hCup : C ≤ 2^(64*20000004*m+1)) :
    cofactorScale 99990001 (2*cofactorDyadicIndex 100000000 (64*20000014*m)) ≤
      D*((X/C)/2^(64*20000014*m)) := by
  have hh := (cofactorDyadicIndex_bounds 100000000 (64*20000014*m) (by decide)).2
  have hexp : 512*99990001*cofactorDyadicIndex 100000000 (64*20000014*m)+
      (64*20000014*m+1) ≤ 64*40000020*m := by nlinarith only [hh,hm]
  have hCQ : C*2^(64*20000014*m) ≤ X := by
    apply (Nat.mul_le_mul_right _ hCup).trans
    apply le_trans _ hX
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  apply le_trans _ (multiplier_floor_half X C D (2^(64*20000014*m)) hC (by positivity) hCD hCQ)
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2*2^(64*20000014*m))).mpr
  apply le_trans _ hX
  rw [cofactorScale_double_index_eq,show 2*2^(64*20000014*m)=(2 : ℕ)^(64*20000014*m+1) by rw [pow_succ]; omega,← pow_add]
  exact Nat.pow_le_pow_right (by decide) hexp

lemma pool_supply_product_upper (m X C D : ℕ)
    (hX : X ≤ independentN 40000021 m) (hDC : D ≤ 2*C) :
    D*((X/C)/2^(64*16080000*m)) ≤
      cofactorScale 150000000 (2*cofactorDyadicIndex 100000000 (64*16080000*m+1)) := by
  have hh := (cofactorDyadicIndex_bounds 100000000 (64*16080000*m+1) (by decide)).1
  have hexp : 64*(40000021-16080000)*m+1 ≤
      512*150000000*cofactorDyadicIndex 100000000 (64*16080000*m+1) := by nlinarith only [hh]
  apply (multiplier_floor_upper X C D (2^(64*16080000*m)) (by positivity) hDC).trans
  apply (Nat.mul_le_mul_left 2 (Nat.div_le_div_right hX)).trans
  have he : independentN 40000021 m = 2^(64*(40000021-16080000)*m)*2^(64*16080000*m) := by
    unfold independentN
    rw [← pow_add]
    congr 1
    omega
  rw [he,Nat.mul_div_cancel _ (by positivity : 0 < (2 : ℕ)^(64*16080000*m)),
    show 2*2^(64*(40000021-16080000)*m)=(2 : ℕ)^(64*(40000021-16080000)*m+1) by rw [pow_succ]; omega,
    cofactorScale_double_index_eq]
  exact Nat.pow_le_pow_right (by decide) hexp

lemma pool_supply_sieve_below_multiplier_primes (m : ℕ) (hm : 1000000 ≤ m) :
    cofactorScale 99990000 (cofactorDyadicIndex 100000000 (64*20000014*m)) < independentN 10000000 m := by
  have hh := (cofactorDyadicIndex_bounds 100000000 (64*20000014*m) (by decide)).2
  have hexp : 256*99990000*cofactorDyadicIndex 100000000 (64*20000014*m) < 64*10000000*m := by
    nlinarith only [hh,hm]
  rw [cofactorScale_eq]
  exact Nat.pow_lt_pow_right (by decide) hexp

end Erdos821.AnalyticSieve
