import Submission.DyadicOrbitClassification
import Submission.CubicBlockRigidity

/-! Consequences for finite words representing complete periods of dyadic
fractions. These do not classify arbitrary good powers of two. -/
namespace Erdos406DyadicPeriodic
open Erdos406DyadicOrbit Erdos406Work Erdos406Structure

lemma good_half_bound (n L : ℕ) (hn : n < 3^L)
    (hg : Nat.digits 3 n ⊆ [0,1]) : 2*n ≤ 3^L-1 := by
  have hh := (digits_iff_no_carries n).mp hg L
  rw [Nat.mod_eq_of_lt hn] at hh
  omega

lemma good_rotate_step (n L : ℕ) (hL : 0 < L) (hn : n < 3^L)
    (hg : Nat.digits 3 n ⊆ [0,1]) :
    Nat.digits 3 (3*n % (3^L-1)) ⊆ [0,1] := by
  let T := 3^(L-1)
  let a := n/T
  let b := n%T
  let D := 3^L-1
  have hT : 0 < T := by dsimp [T]; positivity
  have hpow : 3^L = 3*T := by
    dsimp [T]
    conv_lhs => rw [show L = (L-1)+1 by omega, pow_succ']
  have hD : D+1 = 3*T := by dsimp [D]; omega
  have hn2 := good_half_bound n L hn hg
  have ha : a < 2 := by
    apply (Nat.div_lt_iff_lt_mul hT).mpr
    omega
  have hb : 2*b < T := (digits_iff_no_carries n).mp hg (L-1)
  have hgb : Nat.digits 3 b ⊆ [0,1] := good_mod_three_pow hg (L-1)
  have hga : a ∈ ([0,1] : List ℕ) := by
    rcases Nat.eq_zero_or_pos a with hz | hp
    · simp [hz]
    · have h1 : a = 1 := Nat.le_antisymm (Nat.le_of_lt_succ ha) hp
      simp [h1]
  have hgm : Nat.digits 3 (a+3*b) ⊆ [0,1] := by
    have he : Nat.ofDigits 3 (a :: Nat.digits 3 b) = a+3*b := by simp only [Nat.ofDigits_cons, Nat.ofDigits_digits]
    rw [← he]
    exact good_ofDigits (List.cons_subset.mpr ⟨hga,hgb⟩)
  have hm : a+3*b < D := by omega
  have hdiv : b+T*a = n := Nat.mod_add_div n T
  have he : 3*n = a*D+(a+3*b) := by nlinarith [hdiv, hD]
  change Nat.digits 3 (3*n%D) ⊆ [0,1]
  rw [he, mul_comm a D, Nat.mul_add_mod, Nat.mod_eq_of_lt hm]
  exact hgm

lemma good_rotated_orbit (n L j : ℕ) (hL : 0 < L) (hn : n < 3^L)
    (hg : Nat.digits 3 n ⊆ [0,1]) :
    Nat.digits 3 (3^j*n % (3^L-1)) ⊆ [0,1] := by
  have hp : 1 < 3^L := one_lt_pow₀ (by decide) (by omega)
  have hD : 0 < 3^L-1 := by omega
  induction j with
  | zero =>
    have hh := good_half_bound n L hn hg
    have hsmall : n < 3^L-1 := by omega
    simpa [Nat.mod_eq_of_lt hsmall] using hg
  | succ j ih =>
    have hr := Nat.mod_lt (3^j*n) hD
    have hs := good_rotate_step (3^j*n%(3^L-1)) L hL (by omega) ih
    simpa only [pow_succ', mul_assoc, Nat.mul_mod_mod] using hs

/-- If a good length-L word represents a complete period of a dyadic
fraction, that fraction is one of the four classified orbit points. -/
theorem dyadic_periodic_word_classification (n L a k : ℕ) (hL : 0 < L)
    (hn : n < 3^L) (ha : a < 2^k) (hg : Nat.digits 3 n ⊆ [0,1])
    (he : 2^k*n = a*(3^L-1)) :
    a = 0 ∨ 2*a = 2^k ∨ 8*a = 2^k ∨ 8*a = 3*2^k := by
  apply avoidsTwo_necessary a k ha
  intro j
  have hp : 1 < 3^L := one_lt_pow₀ (by decide) (by omega)
  have hD : 0 < 3^L-1 := by omega
  have hr := Nat.mod_lt (3^j*n) hD
  have hg' := good_rotated_orbit n L j hL hn hg
  have hh := good_half_bound (3^j*n%(3^L-1)) L (by omega) hg'
  have hb : 3*(3^j*n%(3^L-1)) < 2*(3^L-1) := by omega
  have he' := scaled_orbit_remainder n (3^L-1) (2^k) a j he
  have hmul := Nat.mul_lt_mul_of_pos_left hb (show 0 < 2^k by positivity)
  have hfin : (3*(3^j*a%2^k))*(3^L-1) < (2*2^k)*(3^L-1) := by
    nlinarith only [hmul, he']
  exact Nat.lt_of_mul_lt_mul_right hfin

/-- Dividing a ternary repunit-with-digit-two by a power of two can leave
only digits zero and one only for divisors two and eight. -/
theorem good_dyadic_quotient_exponent (n L k : ℕ) (hL : 0 < L)
    (he : 2^k*n = 3^L-1) (hg : Nat.digits 3 n ⊆ [0,1]) : k = 1 ∨ k = 3 := by
  have hp : 1 < 3^L := one_lt_pow₀ (by decide) (by omega)
  have htwo : 1 ≤ 2^k := Nat.one_le_pow _ _ (by decide)
  have hnle : n ≤ 3^L-1 := by
    calc
      n ≤ 2^k*n := Nat.le_mul_of_pos_left _ (by positivity)
      _ = _ := he
  have hn : n < 3^L := by omega
  have hhb := good_half_bound n L hn hg
  have hk : 1 < 2^k := by
    by_contra hk
    have hk1 : 2^k = 1 := by omega
    rw [hk1, one_mul] at he
    omega
  have hc := dyadic_periodic_word_classification n L 1 k hL hn hk hg (by simpa using he)
  norm_num only [Nat.reduceMul, one_ne_zero, false_or] at hc
  rcases hc with h | h | h
  · left
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) (by simpa using h.symm)
  · right
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) (by simpa using h.symm)
  · omega

lemma blockGeom_two_good (t : ℕ) : Nat.digits 3 (blockGeom 2 t) ⊆ [0,1] := by
  have he := ofDigits_repeated_block ([1,0] : List ℕ) t
  norm_num [Nat.ofDigits] at he
  rw [← he]
  apply good_ofDigits
  intro d hd
  obtain ⟨w, hw, hdw⟩ := List.mem_flatten.mp hd
  simp only [List.mem_replicate] at hw
  simpa [hw.2, or_comm] using hdw

lemma blockGeom_two_identity (t : ℕ) : 8*blockGeom 2 t+1 = 3^(2*t) := by
  induction t with
  | zero => simp [blockGeom]
  | succ t ih =>
    rw [blockGeom_succ]
    rw [show 2*(t+1) = 2*t+2 by omega, pow_add]
    norm_num
    nlinarith

/-- Exact classification for this periodic quotient family. The divisibility
premise is essential and is not known for arbitrary candidate words. -/
theorem good_dyadic_quotient_iff (L k : ℕ) (hL : 0 < L) (hd : 2^k ∣ 3^L-1) :
    Nat.digits 3 ((3^L-1)/2^k) ⊆ [0,1] ↔ k = 1 ∨ k = 3 := by
  have hp : 1 < 3^L := one_lt_pow₀ (by decide) (by omega)
  have he := Nat.mul_div_cancel' hd
  constructor
  · exact good_dyadic_quotient_exponent _ L k hL he
  · rintro (rfl | rfl)
    · have hR := Erdos406Structure.ternaryRepunit_identity L
      have heq : (3^L-1)/2 = Erdos406Structure.ternaryRepunit L := by omega
      change Nat.digits 3 ((3^L-1)/2) ⊆ [0,1]
      rw [heq]
      exact Erdos406Structure.ternaryRepunit_good L
    · have hEven : Even L := by
        rcases Nat.even_or_odd L with h | ⟨t, ht⟩
        · exact h
        · have hm : 3^L%8 = 3 := by
            rw [ht, pow_add, pow_mul]
            norm_num [Nat.mul_mod, Nat.pow_mod]
          have hh := Nat.mod_eq_zero_of_dvd hd
          norm_num only [show (2 : ℕ)^3 = 8 by decide] at hh
          omega
      obtain ⟨t, ht⟩ := hEven
      have hL' : L = 2*t := by omega
      have hi := blockGeom_two_identity t
      have heq : (3^L-1)/2^3 = blockGeom 2 t := by rw [hL']; norm_num; omega
      rw [heq]
      exact blockGeom_two_good t

#print axioms good_rotated_orbit
#print axioms dyadic_periodic_word_classification
#print axioms good_dyadic_quotient_iff
end Erdos406DyadicPeriodic
