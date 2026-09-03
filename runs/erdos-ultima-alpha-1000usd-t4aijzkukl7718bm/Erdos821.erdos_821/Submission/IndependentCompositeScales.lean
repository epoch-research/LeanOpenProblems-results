import Submission.EndpointCompositeGain

/-!
# Independent block-factor and smoothness parameters

All parameters in the estimates below are fixed before the scale tends to infinity.
This separates the number of prescribed block-prime factors from the cutoff exponent.
-/

open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

def independentN (t m : ℕ) : ℕ := 2^(64*t*m)
def independentJ (b m : ℕ) : ℕ := (b-1)*m

noncomputable def independentSieveError (r b h m : ℕ) : ℝ :=
  ((primeProductModuli r m).card : ℝ) * (2 : ℝ)^(64*h*m) *
    ((2 : ℝ)^(64*independentJ b m) + (2 : ℝ)^(16*independentJ b m) + 1)

noncomputable def independentSieveMain (t b h m : ℕ) : ℝ :=
  (2/675 : ℝ) * (independentN t m : ℝ) *
    (harmonic (2^(64*h*m)) : ℝ) / ((independentJ b m : ℝ)*Real.log 2)^2

def independentErrorConstant (r t : ℕ) : ℕ :=
  64*t*(3*2^(64*r)+2*(t-1).choose r)

lemma independent_log_upper (t m : ℕ) :
    Real.log (independentN t m : ℝ) ≤ 64*(t : ℝ)*((m : ℝ)+1) := by
  have h := log_two_pow_le (64*t*m)
  change Real.log (independentN t m : ℝ) ≤ _ at h
  simp only [Nat.cast_mul, Nat.cast_ofNat] at h
  nlinarith only [h, Nat.cast_nonneg (α := ℝ) t]

lemma independent_sieve_error_pow_bound (r t b h m : ℕ)
    (heq : r+b+h=t) (hb : 1 ≤ b) :
    independentSieveError r b h m ≤
      (3*(2 : ℝ)^(64*r))*(2 : ℝ)^((64*t-1)*m) := by
  have ht : 1 ≤ t := by omega
  have hcard : ((primeProductModuli r m).card : ℝ) ≤ (2 : ℝ)^(64*r*(m+1)) := by
    have hh := primeProductModuli_card_le_upper r m
    have he : progressionScaleN (m+1)^r = 2^(64*r*(m+1)) := by
      simp only [progressionScaleN, ← pow_mul]
      congr 1
      ring
    rw [he] at hh
    exact_mod_cast hh
  have hJpow : (2 : ℝ)^(16*independentJ b m) ≤ (2 : ℝ)^(64*independentJ b m) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hJone : (1 : ℝ) ≤ (2 : ℝ)^(64*independentJ b m) := one_le_pow₀ (by norm_num)
  have hE : (2 : ℝ)^(64*independentJ b m) +
      (2 : ℝ)^(16*independentJ b m) + 1 ≤ 3*(2 : ℝ)^(64*independentJ b m) := by
    linarith only [hJpow, hJone]
  have hexp : 64*r*(m+1)+64*h*m+64*independentJ b m ≤ 64*r+(64*t-1)*m := by
    dsimp only [independentJ]
    have hsub := congrArg (fun z : ℕ => z*m) (Nat.sub_add_cancel hb)
    have hsubt := congrArg (fun z : ℕ => z*m)
      (Nat.sub_add_cancel (by omega : 1 ≤ 64*t))
    have ht' := congrArg (fun z : ℕ => z*m) heq
    nlinarith only [hsub, hsubt, ht', Nat.zero_le m]
  have hpow : (2 : ℝ)^(64*r*(m+1))*(2 : ℝ)^(64*h*m)*
      (2 : ℝ)^(64*independentJ b m) ≤
        (2 : ℝ)^(64*r)*(2 : ℝ)^((64*t-1)*m) := by
    simp only [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) hexp
  unfold independentSieveError
  calc
    _ ≤ (2 : ℝ)^(64*r*(m+1))*(2 : ℝ)^(64*h*m)*
        (3*(2 : ℝ)^(64*independentJ b m)) := by gcongr
    _ = 3*((2 : ℝ)^(64*r*(m+1))*(2 : ℝ)^(64*h*m)*
        (2 : ℝ)^(64*independentJ b m)) := by ring
    _ ≤ 3*((2 : ℝ)^(64*r)*(2 : ℝ)^((64*t-1)*m)) := by gcongr
    _ = _ := by ring

lemma independent_sqrt_pow_bound (t m : ℕ) (ht : 1 ≤ t) :
    Real.sqrt (independentN t m : ℝ) ≤ (2 : ℝ)^((64*t-1)*m) := by
  have heq : independentN t m = progressionScaleN (t*m) := by
    simp only [independentN, progressionScaleN, mul_assoc]
  rw [heq, sqrt_progressionScaleN]
  apply pow_le_pow_right₀ (by norm_num)
  have hcoef : 32*t ≤ 64*t-1 := by omega
  simpa only [mul_assoc] using Nat.mul_le_mul_right m hcoef

lemma independent_total_error_pow_bound (r t b h m : ℕ)
    (heq : r+b+h=t) (hb : 1 ≤ b) :
    Real.log (independentN t m : ℝ) *
      (independentSieveError r b h m +
        2*((t-1).choose r : ℝ)*Real.sqrt (independentN t m : ℝ)) ≤
      (independentErrorConstant r t : ℝ)*((m : ℝ)+1)*(2 : ℝ)^((64*t-1)*m) := by
  have hlog := independent_log_upper t m
  have hE := independent_sieve_error_pow_bound r t b h m heq hb
  have hsqrt := independent_sqrt_pow_bound t m (by omega)
  have hlog0 := Real.log_natCast_nonneg (independentN t m)
  have hB0 : (0 : ℝ) ≤ (t-1).choose r := Nat.cast_nonneg _
  calc
    _ ≤ Real.log (independentN t m : ℝ)*
        ((3*(2 : ℝ)^(64*r))*(2 : ℝ)^((64*t-1)*m)+
          2*((t-1).choose r : ℝ)*(2 : ℝ)^((64*t-1)*m)) := by gcongr
    _ ≤ (64*(t : ℝ)*((m : ℝ)+1))*
        ((3*(2 : ℝ)^(64*r))*(2 : ℝ)^((64*t-1)*m)+
          2*((t-1).choose r : ℝ)*(2 : ℝ)^((64*t-1)*m)) := by gcongr
    _ = _ := by
      simp only [independentErrorConstant, Nat.cast_mul, Nat.cast_add,
        Nat.cast_pow, Nat.cast_ofNat]
      ring

lemma eventually_independent_total_error_small (r t b h : ℕ)
    (heq : r+b+h=t) (hb : 1 ≤ b) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (independentN t m : ℝ)*
        (independentSieveError r b h m +
          2*((t-1).choose r : ℝ)*Real.sqrt (independentN t m : ℝ)) ≤
        (independentN t m : ℝ)/64*primeProductReciprocalMass r m := by
  filter_upwards [eventually_nat_poly_le_two_pow 1
      (64*primeProductMassConstant r*independentErrorConstant r t) (r+1),
    eventually_product_reciprocal_supply r] with m hpoly hmass
  let C : ℝ := primeProductMassConstant r
  let E : ℝ := independentErrorConstant r t
  let z : ℝ := (m : ℝ)+1
  let R : ℝ := (2 : ℝ)^((64*t-1)*m)
  let N := independentN t m
  have hC : 0 < C := by dsimp only [C]; exact_mod_cast primeProductMassConstant_pos r
  have hz : 0 < z := by dsimp only [z]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hpolyR : 64*C*E*z^(r+1) ≤ (2 : ℝ)^m := by
    dsimp only [C, E, z]
    simpa only [one_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat, Nat.cast_pow] using
      (show (((64*primeProductMassConstant r*independentErrorConstant r t)*
        (1*m+1)^(r+1) : ℕ) : ℝ) ≤ ((2^m : ℕ) : ℝ) from by exact_mod_cast hpoly)
  have hpow : (2 : ℝ)^m*R = (N : ℝ) := by
    simp only [R, N, independentN, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
    congr 1
    have hh := congrArg (fun z : ℕ => z*m)
      (Nat.sub_add_cancel (by omega : 1 ≤ 64*t))
    nlinarith only [hh]
  have hbudget : E*z*R ≤ (N : ℝ)/(64*C*z^r) := by
    apply (le_div_iff₀ (by positivity : 0 < 64*C*z^r)).mpr
    calc
      _ = (64*C*E*z^(r+1))*R := by rw [pow_succ]; ring
      _ ≤ (2 : ℝ)^m*R := mul_le_mul_of_nonneg_right hpolyR hR
      _ = _ := hpow
  calc
    _ ≤ E*z*R := independent_total_error_pow_bound r t b h m heq hb
    _ ≤ (N : ℝ)/(64*C*z^r) := hbudget
    _ = (N : ℝ)/64*(1/(C*z^r)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass
      (div_nonneg (Nat.cast_nonneg _) (by norm_num))

lemma independent_count_of_weight (r t b m : ℕ)
    (hmass : 1/((primeProductMassConstant r : ℝ)*((m : ℝ)+1)^r) ≤
      primeProductReciprocalMass r m)
    (hweight : (independentN t m : ℝ)/64*primeProductReciprocalMass r m ≤
      ((t-1).choose r : ℝ)*Real.log (independentN t m : ℝ)*
        ((smoothStructuredPrimes r m (independentN t m) (independentN b m)).card : ℝ)) :
    independentN t m ≤ (2*structuredPrimeCountConstant r t)*
      (m+1)^(r+1)*(smoothStructuredPrimes r m (independentN t m) (independentN b m)).card := by
  let N := independentN t m
  let C : ℝ := primeProductMassConstant r
  let B : ℝ := (t-1).choose r
  let z : ℝ := (m : ℝ)+1
  let G := smoothStructuredPrimes r m (independentN t m) (independentN b m)
  have hC : 0 < C := by dsimp only [C]; exact_mod_cast primeProductMassConstant_pos r
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hz : 0 < z := by dsimp only [z]; positivity
  have hlog : Real.log (N : ℝ) ≤ 64*(t : ℝ)*z := independent_log_upper t m
  have hgood : (N : ℝ)/(64*C*z^r) ≤ B*Real.log N*(G.card : ℝ) := by
    calc
      _ = (N : ℝ)/64*(1/(C*z^r)) := by ring
      _ ≤ (N : ℝ)/64*primeProductReciprocalMass r m :=
        mul_le_mul_of_nonneg_left hmass (div_nonneg (Nat.cast_nonneg _) (by norm_num))
      _ ≤ _ := hweight
  have hgood' := hgood.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hB) (Nat.cast_nonneg G.card))
  have hfinal := (div_le_iff₀ (by positivity : 0 < 64*C*z^r)).mp hgood'
  have hfinal' : (N : ℝ) ≤ (2*structuredPrimeCountConstant r t : ℕ)*
      z^(r+1)*(G.card : ℝ) := by
    simp only [structuredPrimeCountConstant, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
    dsimp only [C, B] at hfinal
    nlinarith only [hfinal]
  dsimp only [N, G, z] at hfinal'
  exact_mod_cast hfinal'

end Erdos821
