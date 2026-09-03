import Submission.ChebyshevCompositeGain

/-!
# Flexible Chebyshev weights and arbitrarily small relative errors

These estimates preserve the full factorial-ratio constant and allow fixed
positive margins to be chosen before the scale tends to infinity.
-/
open Nat Finset ArithmeticFunction Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma eventually_mangoldt_lower_constant (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c < chebyshevRatioConstant) :
    ∀ᶠ N : ℕ in atTop, c*(N : ℝ) ≤ mangoldtSum N := by
  let d : ℝ := (chebyshevRatioConstant+c)/2
  have hclo : (c : ℝ) < d := by
    dsimp [d]
    linarith [hc]
  have hchi : d < chebyshevRatioConstant := by
    dsimp [d]
    linarith [hc]
  have hd : 0 < d := by linarith
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (tendsto_chebyshevFactorialRatio_div.eventually (eventually_ge_nhds hchi))
  have hlim : Tendsto (fun N : ℕ => (d-c)*(N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith)
  filter_upwards [eventually_ge_atTop (30*(M+1)),
    hlim.eventually (eventually_ge_atTop (30*d))] with N hN hbudget
  let m := N/30
  have hm : M ≤ m := by dsimp [m]; omega
  have hm0 : 0 < m := by dsimp [m]; omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hh : d*(30*(m : ℝ)) ≤ chebyshevFactorialRatio m := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 30*(m : ℝ))).mp (hM m hm)
    exact h
  have hsmall : 30*m ≤ N := Nat.mul_div_le N 30
  have hclose : (N : ℝ)-30 ≤ 30*(m : ℝ) := by
    have hnat : N ≤ 30*m+30 := by dsimp [m]; omega
    have hreal : (N : ℝ) ≤ 30*(m : ℝ)+30 := by exact_mod_cast hnat
    linarith only [hreal]
  have hmain : d*(30*(m : ℝ)) ≤ mangoldtSum N :=
    hh.trans ((chebyshevFactorialRatio_le_mangoldt m).trans (mangoldtSum_mono hsmall))
  have hprod := mul_le_mul_of_nonneg_left hclose hd.le
  nlinarith only [hmain, hprod, hbudget]

lemma eventually_progression_mangoldt_lower_constant (t : ℕ) (ht : 1 ≤ t)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < chebyshevRatioConstant) :
    ∀ᶠ m : ℕ in atTop,
      c*(progressionScaleN (t*m) : ℝ) ≤ mangoldtSum (progressionScaleN (t*m)) := by
  have hlim : Tendsto (fun m : ℕ => progressionScaleN (t*m)) atTop atTop := by
    apply tendsto_atTop_mono (fun m => ?_) tendsto_id
    apply Nat.lt_two_pow_self.le.trans
    apply Nat.pow_le_pow_right (by decide)
    change m ≤ 64*(t*m)
    exact (Nat.le_mul_of_pos_left m (by omega : 0 < t)).trans
      (Nat.le_mul_of_pos_left (t*m) (by decide))
  exact hlim.eventually (eventually_mangoldt_lower_constant c hc0 hc)

lemma eventually_product_mangoldt_lower_constant (r t : ℕ) (hrt : 2*r+1 ≤ t)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < chebyshevRatioConstant) :
    ∀ᶠ m : ℕ in atTop,
      c*(progressionScaleN (t*m) : ℝ)*primeProductReciprocalMass r m ≤
        ∑ d ∈ primeProductModuli r m, residueOneMangoldt d (progressionScaleN (t*m)) := by
  let a := (c+chebyshevRatioConstant)/2
  have hca : c < a := by dsimp [a]; linarith
  have hac : a < chebyshevRatioConstant := by dsimp [a]; linarith
  have ha0 : 0 ≤ a := hc0.trans hca.le
  have hgap : 0 < a-c := sub_pos.mpr hca
  have hlim : Tendsto (fun m : ℕ => (a-c)*((m : ℝ)+1)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop hgap
  filter_upwards [eventually_progression_mangoldt_lower_constant t (by omega) a ha0 hac,
    eventually_product_mangoldt_total_lower r t (r+1) hrt,
    eventually_product_reciprocal_supply r,
    hlim.eventually (eventually_ge_atTop (primeProductMassConstant r : ℝ))]
      with m hpsi htotal hmass hbudget
  let N := progressionScaleN (t*m)
  let C : ℝ := primeProductMassConstant r
  let z : ℝ := (m : ℝ)+1
  have hC : 0 < C := by dsimp only [C]; exact_mod_cast primeProductMassConstant_pos r
  have hz : 0 < z := by dsimp [z]; positivity
  have hW : 0 ≤ primeProductReciprocalMass r m :=
    (by positivity : 0 ≤ 1/(C*z^r)).trans hmass
  have herr : (N : ℝ)/z^(r+1) ≤ (a-c)*(N : ℝ)*primeProductReciprocalMass r m := by
    have hcoeff : (1 : ℝ)/z^(r+1) ≤ (a-c)*(1/(C*z^r)) := by
      apply (div_le_iff₀ (pow_pos hz _)).mpr
      have he : (a-c)*(1/(C*z^r))*z^(r+1) = (a-c)*z/C := by
        rw [pow_succ]; field_simp
      rw [he]
      exact (le_div_iff₀ hC).mpr (by simpa only [one_mul] using hbudget)
    calc
      _ = (N : ℝ)*(1/z^(r+1)) := by ring
      _ ≤ (N : ℝ)*((a-c)*(1/(C*z^r))) := mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg _)
      _ ≤ (N : ℝ)*((a-c)*primeProductReciprocalMass r m) := by gcongr
      _ = _ := by ring
  have hmain := mul_le_mul_of_nonneg_right hpsi hW
  change a*(N : ℝ)*primeProductReciprocalMass r m ≤ _ at hmain
  change mangoldtSum N*primeProductReciprocalMass r m-(N : ℝ)/z^(r+1) ≤ _ at htotal
  change c*(N : ℝ)*primeProductReciprocalMass r m ≤ _
  nlinarith only [hmain,herr,htotal]

lemma eventually_independent_total_error_divisor (r t b h D : ℕ)
    (heq : r+b+h=t) (hb : 1 ≤ b) (hD : 0 < D) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (independentN t m : ℝ)*
        (independentSieveError r b h m +
          2*((t-1).choose r : ℝ)*Real.sqrt (independentN t m : ℝ)) ≤
        (independentN t m : ℝ)/(D : ℝ)*primeProductReciprocalMass r m := by
  filter_upwards [eventually_nat_poly_le_two_pow 1
      (D*primeProductMassConstant r*independentErrorConstant r t) (r+1),
    eventually_product_reciprocal_supply r] with m hpoly hmass
  let C : ℝ := primeProductMassConstant r
  let E : ℝ := independentErrorConstant r t
  let z : ℝ := (m : ℝ)+1
  let R : ℝ := (2 : ℝ)^((64*t-1)*m)
  let N := independentN t m
  have hC : 0 < C := by dsimp only [C]; exact_mod_cast primeProductMassConstant_pos r
  have hz : 0 < z := by dsimp only [z]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hpolyR : (D : ℝ)*C*E*z^(r+1) ≤ (2 : ℝ)^m := by
    dsimp only [C, E, z]
    simpa only [one_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat, Nat.cast_pow] using
      (show (((D*primeProductMassConstant r*independentErrorConstant r t)*
        (1*m+1)^(r+1) : ℕ) : ℝ) ≤ ((2^m : ℕ) : ℝ) from by exact_mod_cast hpoly)
  have hpow : (2 : ℝ)^m*R = (N : ℝ) := by
    simp only [R, N, independentN, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
    congr 1
    have hh := congrArg (fun z : ℕ => z*m)
      (Nat.sub_add_cancel (by omega : 1 ≤ 64*t))
    nlinarith only [hh]
  have hbudget : E*z*R ≤ (N : ℝ)/((D : ℝ)*C*z^r) := by
    apply (le_div_iff₀ (by positivity : 0 < (D : ℝ)*C*z^r)).mpr
    calc
      _ = ((D : ℝ)*C*E*z^(r+1))*R := by rw [pow_succ]; ring
      _ ≤ (2 : ℝ)^m*R := mul_le_mul_of_nonneg_right hpolyR hR
      _ = _ := hpow
  calc
    _ ≤ E*z*R := independent_total_error_pow_bound r t b h m heq hb
    _ ≤ (N : ℝ)/((D : ℝ)*C*z^r) := hbudget
    _ = (N : ℝ)/(D : ℝ)*(1/(C*z^r)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass
      (div_nonneg (Nat.cast_nonneg _) (by positivity))

def flexibleStructuredCountConstant (r t D : ℕ) : ℕ :=
  64*D*primeProductMassConstant r*t*(t-1).choose r

lemma flexible_independent_count_of_weight (r t b m D : ℕ) (hD : 0 < D)
    (hmass : 1/((primeProductMassConstant r : ℝ)*((m : ℝ)+1)^r) ≤
      primeProductReciprocalMass r m)
    (hweight : (independentN t m : ℝ)/(D : ℝ)*primeProductReciprocalMass r m ≤
      ((t-1).choose r : ℝ)*Real.log (independentN t m : ℝ)*
        ((smoothStructuredPrimes r m (independentN t m) (independentN b m)).card : ℝ)) :
    independentN t m ≤ flexibleStructuredCountConstant r t D*
      (m+1)^(r+1)*(smoothStructuredPrimes r m (independentN t m) (independentN b m)).card := by
  let N := independentN t m
  let C : ℝ := primeProductMassConstant r
  let B : ℝ := (t-1).choose r
  let z : ℝ := (m : ℝ)+1
  let G := smoothStructuredPrimes r m (independentN t m) (independentN b m)
  have hC : 0 < C := by dsimp only [C]; exact_mod_cast primeProductMassConstant_pos r
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hz : 0 < z := by dsimp [z]; positivity
  have hlog : Real.log (N : ℝ) ≤ 64*(t : ℝ)*z := independent_log_upper t m
  have hgood : (N : ℝ)/((D : ℝ)*C*z^r) ≤ B*Real.log N*(G.card : ℝ) := by
    calc
      _ = (N : ℝ)/(D : ℝ)*(1/(C*z^r)) := by ring
      _ ≤ (N : ℝ)/(D : ℝ)*primeProductReciprocalMass r m :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ ≤ _ := hweight
  have hgood' := hgood.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hB) (Nat.cast_nonneg G.card))
  have hfinal := (div_le_iff₀ (by positivity : 0 < (D : ℝ)*C*z^r)).mp hgood'
  have hfinal' : (N : ℝ) ≤ (flexibleStructuredCountConstant r t D : ℝ)*z^(r+1)*(G.card : ℝ) := by
    simp only [flexibleStructuredCountConstant, Nat.cast_mul, Nat.cast_ofNat,pow_succ]
    dsimp only [C,B] at hfinal
    nlinarith only [hfinal]
  dsimp only [N,G,z] at hfinal'
  exact_mod_cast hfinal'

end Erdos821
