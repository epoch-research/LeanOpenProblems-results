import Submission.UnimodularBoxCounts

/-! A common-divisor sieve preserving a fixed proportion of a unimodular
quartic congruence count in a larger box. -/
namespace Erdos322Research.QuarticDivisorSieve
noncomputable section
open Finset UnimodularRootCRT UnimodularBoxCounts
open scoped Classical
set_option Elab.async false
set_option maxHeartbeats 0

lemma reciprocal_fourth_small (x : ℝ) (hx : 1≤x) :
    1/(x+1)^4 ≤ (1/8)*(1/x-1/(x+1)) := by
  have hx0 : 0<x := by linarith
  have hx1 : 0<x+1 := by linarith
  have hcube : 8*x≤(x+1)^3 := by
    have hm := mul_nonneg (by linarith : 0≤x-1) (by nlinarith : 0≤x^2+4*x-1)
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hcube hx1.le
  calc
    1/(x+1)^4 ≤ 1/(8*x*(x+1)) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    _ = (1/8)*(1/x-1/(x+1)) := by field_simp; ring

lemma reciprocal_fourth_tail (x : ℝ) (hx : 1≤x) :
    1/(x+1)^4 ≤ 1/x^3-1/(x+1)^3 := by
  have hx0 : 0<x := by linarith
  have hx1 : 0<x+1 := by linarith
  apply (le_sub_iff_add_le).mpr
  have he : 1/(x+1)^4+1/(x+1)^3=(x+2)/(x+1)^4 := by field_simp; ring
  rw [he]
  apply (div_le_div_iff₀ (by positivity : 0<(x+1)^4) (by positivity : 0<x^3)).mpr
  nlinarith [sq_nonneg x, pow_nonneg hx0.le 3]

lemma sum_reciprocal_fourth_small (D : ℕ) (hD : 1≤D) :
    ∑ d ∈ Ico 2 (D+1), (1 : ℝ)/d^4 ≤ 1/8 := by
  rw [← Finset.sum_Ico_add' (fun d : ℕ ↦ (1 : ℝ)/d^4) 1 D 1]
  have hh : ∑ d ∈ Ico 1 D, (1 : ℝ)/(d+1)^4 ≤
      (1/8)*(∑ d ∈ Ico 1 D, ((1 : ℝ)/d-1/(d+1))) := by
    rw [mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    exact reciprocal_fourth_small d (by exact_mod_cast (mem_Ico.mp hd).1)
  push_cast
  have ht := Finset.sum_Ico_sub (fun d : ℕ ↦ -((1 : ℝ)/d)) hD
  have ht' : (∑ d ∈ Ico 1 D, ((1 : ℝ)/d-1/(d+1)))=1-1/D := by
    simpa only [Nat.cast_add,Nat.cast_one,neg_sub_neg,Nat.cast_one,div_one] using ht
  rw [ht'] at hh
  have hn : (0 : ℝ)≤1/D := by positivity
  linarith

lemma sum_reciprocal_fourth_tail (D B : ℕ) (hD : 1≤D) (hDB : D≤B) :
    ∑ d ∈ Ico (D+1) (B+1), (1 : ℝ)/d^4 ≤ 1/(D : ℝ)^3 := by
  rw [← Finset.sum_Ico_add' (fun d : ℕ ↦ (1 : ℝ)/d^4) D B 1]
  push_cast
  have hh : ∑ d ∈ Ico D B, (1 : ℝ)/(d+1)^4 ≤
      ∑ d ∈ Ico D B, ((1 : ℝ)/d^3-1/(d+1)^3) := by
    apply Finset.sum_le_sum
    intro d hd
    exact reciprocal_fourth_tail d (by exact_mod_cast hD.trans (mem_Ico.mp hd).1)
  have ht := Finset.sum_Ico_sub (fun d : ℕ ↦ -((1 : ℝ)/d^3)) hDB
  have ht' : (∑ d ∈ Ico D B, ((1 : ℝ)/d^3-1/(d+1)^3))=1/(D : ℝ)^3-1/(B : ℝ)^3 := by
    simpa only [Nat.cast_add,Nat.cast_one,neg_sub_neg] using ht
  rw [ht'] at hh
  have hn : (0 : ℝ)≤1/(B : ℝ)^3 := by positivity
  linarith

lemma modular_small_bound (q T d : ℕ) [NeZero q] (hd : 0<d) (hdT : 2*d≤T) :
    (divisorCount 4 q (q*T) d : ℝ) ≤
      (81/16)*(count 4 q : ℝ)*(T : ℝ)^4*((1 : ℝ)/d^4) := by
  have hq : 0<q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hb := divisor_bound_modular 4 q (q*T) d
  rw [mul_comm d q,Nat.mul_div_mul_left _ _ hq] at hb
  have hb' : (divisorCount 4 q (q*T) d : ℝ) ≤ (count 4 q : ℝ)*((T/d : ℕ)+1)^4 := by exact_mod_cast hb
  have hd0 : (0 : ℝ)<d := by exact_mod_cast hd
  have hdT' : 2*(d : ℝ)≤T := by exact_mod_cast hdT
  have hfloor : ((T/d : ℕ) : ℝ)+1 ≤ 3*(T : ℝ)/(2*d) := by
    have hdiv : ((T/d : ℕ) : ℝ)≤(T : ℝ)/d := Nat.cast_div_le
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<2*d)).mpr
    have hh := (le_div_iff₀ hd0).mp hdiv
    nlinarith
  calc
    (divisorCount 4 q (q*T) d : ℝ) ≤ (count 4 q : ℝ)*((T/d : ℕ)+1)^4 := hb'
    _ ≤ (count 4 q : ℝ)*(3*(T : ℝ)/(2*d))^4 := by gcongr
    _ = (81/16)*(count 4 q : ℝ)*(T : ℝ)^4*((1 : ℝ)/d^4) := by field_simp; ring

lemma box_large_bound (q B d : ℕ) (hd : 0<d) (hdB : d≤B) :
    (divisorCount 4 q B d : ℝ) ≤ 16*(B : ℝ)^4*((1 : ℝ)/d^4) := by
  have hb' : (divisorCount 4 q B d : ℝ) ≤ ((B/d : ℕ)+1)^4 := by
    exact_mod_cast divisor_bound_box 4 q B d
  have hd0 : (0 : ℝ)<d := by exact_mod_cast hd
  have hdB' : (d : ℝ)≤B := by exact_mod_cast hdB
  have hfloor : ((B/d : ℕ) : ℝ)+1 ≤ 2*(B : ℝ)/d := by
    have hdiv : ((B/d : ℕ) : ℝ)≤(B : ℝ)/d := Nat.cast_div_le
    apply (le_div_iff₀ hd0).mpr
    have hh := (le_div_iff₀ hd0).mp hdiv
    nlinarith
  calc
    (divisorCount 4 q B d : ℝ) ≤ ((B/d : ℕ)+1)^4 := hb'
    _ ≤ (2*(B : ℝ)/d)^4 := by gcongr
    _ = 16*(B : ℝ)^4*((1 : ℝ)/d^4) := by field_simp; ring

/-- For q at least two, the box of side 16 q squared retains a quarter of
the main term as globally primitive tuples. -/
theorem primitive_box_lower (q : ℕ) [NeZero q] (hq : 1<q)
    (hcount : q ≤ count 4 q) :
    (count 4 q : ℝ)*(16*q : ℝ)^4/4 ≤ primitiveBoxCount 4 q (q*(16*q)) := by
  let T := 16*q
  let D := 8*q
  let B := q*T
  have hq0 : (0 : ℝ)<q := by exact_mod_cast lt_trans (by decide : 0<1) hq
  have hD : 1≤D := by dsimp only [D]; omega
  have hDB : D≤B := by dsimp only [D,B,T]; nlinarith
  have hsmall : (∑ d ∈ Ico 2 (D+1), (divisorCount 4 q B d : ℝ)) ≤
      (81/128)*(count 4 q : ℝ)*(T : ℝ)^4 := by
    calc
      (∑ d ∈ Ico 2 (D+1), (divisorCount 4 q B d : ℝ)) ≤
          ∑ d ∈ Ico 2 (D+1), (81/16)*(count 4 q : ℝ)*(T : ℝ)^4*((1 : ℝ)/d^4) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd' := mem_Ico.mp hd
        exact modular_small_bound q T d (by omega) (by dsimp only [D,T] at *; omega)
      _ = (81/16)*(count 4 q : ℝ)*(T : ℝ)^4*(∑ d ∈ Ico 2 (D+1), (1 : ℝ)/d^4) := by rw [mul_sum]
      _ ≤ (81/16)*(count 4 q : ℝ)*(T : ℝ)^4*(1/8) := by
        gcongr
        exact sum_reciprocal_fourth_small D hD
      _ = _ := by ring
  have hlarge : (∑ d ∈ Ico (D+1) (B+1), (divisorCount 4 q B d : ℝ)) ≤
      (1/32)*(count 4 q : ℝ)*(T : ℝ)^4 := by
    calc
      (∑ d ∈ Ico (D+1) (B+1), (divisorCount 4 q B d : ℝ)) ≤
          ∑ d ∈ Ico (D+1) (B+1), 16*(B : ℝ)^4*((1 : ℝ)/d^4) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd' := mem_Ico.mp hd
        exact box_large_bound q B d (by omega) (by omega)
      _ = 16*(B : ℝ)^4*(∑ d ∈ Ico (D+1) (B+1), (1 : ℝ)/d^4) := by rw [mul_sum]
      _ ≤ 16*(B : ℝ)^4*(1/(D : ℝ)^3) := by
        gcongr
        exact sum_reciprocal_fourth_tail D B hD hDB
      _ = (1/32)*(q : ℝ)*(T : ℝ)^4 := by
        dsimp only [B,D]
        push_cast
        field_simp
        ring
      _ ≤ _ := by gcongr
  have hsplit : (∑ d ∈ Icc 2 B, (divisorCount 4 q B d : ℝ)) =
      (∑ d ∈ Ico 2 (D+1), (divisorCount 4 q B d : ℝ))+
      (∑ d ∈ Ico (D+1) (B+1), (divisorCount 4 q B d : ℝ)) := by
    rw [Finset.sum_Ico_consecutive _ (by omega : 2≤D+1) (by omega : D+1≤B+1)]
    congr 1
  have htotal : (count 4 q : ℝ)*(T : ℝ)^4 ≤ boxCount 4 q B := by exact_mod_cast lift_lower 4 q T
  have hsieve : (boxCount 4 q B : ℝ) ≤ primitiveBoxCount 4 q B+
      ∑ d ∈ Icc 2 B, (divisorCount 4 q B d : ℝ) := by exact_mod_cast box_le_primitive_add_divisors 4 q B hq
  rw [hsplit] at hsieve
  have hn : (0 : ℝ)≤(count 4 q : ℝ)*(T : ℝ)^4 := by positivity
  have hmain : (count 4 q : ℝ)*(T : ℝ)^4/4 ≤ primitiveBoxCount 4 q B := by nlinarith
  simpa only [T,B,Nat.cast_mul,Nat.cast_ofNat] using hmain

end
end Erdos322Research.QuarticDivisorSieve
