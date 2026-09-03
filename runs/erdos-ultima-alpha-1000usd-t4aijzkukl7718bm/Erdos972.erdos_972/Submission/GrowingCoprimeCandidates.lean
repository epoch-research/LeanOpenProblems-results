import Submission.DualPrimeRows
import Submission.PrimeFejer
import Submission.CorrelationVaughan

/-!
A positive lower bound for prime inputs whose outputs avoid a growing modulus.
The output is only required to be coprime to that modulus, not prime.
-/
namespace Erdos972GrowingCoprimeCandidates

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972WeightedPrimeRotation
open Erdos972PrimeFejer Erdos972ScaledPrimeRows Erdos972PolynomialRowScales
open Erdos972PrimeRotation Erdos972DualPrimeRows Erdos972ChebyshevPNT

set_option maxHeartbeats 1000000

noncomputable def coprimePrimeWeight (α : ℝ) (D N : ℕ) : ℝ :=
  ∑ n ∈ (Ioc 0 N).filter (fun n => n.Prime ∧ (floorMul α n).Coprime D), Real.log n

lemma coprimePrimeWeight_one (α : ℝ) (N : ℕ) :
    coprimePrimeWeight α 1 N = Chebyshev.theta N := by
  simp [coprimePrimeWeight, Chebyshev.theta]

lemma arc_le_coprimePrimeWeight_add_prime_powers (α θ t a b : ℝ) (D N : ℕ)
    (hcop : ∀ n ∈ Ioc 0 N,
      a ≤ Int.fract (θ*n+t) → Int.fract (θ*n+t) < b → (floorMul α n).Coprime D) :
    mangoldtArcSum θ t a b N ≤ coprimePrimeWeight α D N +
      (Chebyshev.psi N - Chebyshev.theta N) := by
  classical
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
  simp only [mangoldtArcSum, coprimePrimeWeight, sum_filter, ← sum_add_distrib]
  apply sum_le_sum
  intro n hn
  by_cases ha : a ≤ Int.fract (θ*n+t) ∧ Int.fract (θ*n+t) < b
  · by_cases hp : n.Prime
    · have hc := hcop n hn ha.1 ha.2
      rw [if_pos ha, if_pos ⟨hp, hc⟩, if_neg (not_not.mpr hp)]
      simp only [vonMangoldt_apply_prime hp, add_zero, le_refl]
    · simp [ha, hp]
  · simp only [ha, if_false]
    apply add_nonneg
    · split_ifs <;> first | exact Real.log_natCast_nonneg _ | exact le_rfl
    · split_ifs <;> first | exact vonMangoldt_nonneg | exact le_rfl

lemma coprime_arc (α : ℝ) (hα : 0 ≤ α) {D : ℕ} (hD : 0 < D) (n : ℕ)
    (hlo : 5/(4*(D : ℝ)) ≤ Int.fract ((2+α/D)*n))
    (hhi : Int.fract ((2+α/D)*n) < 7/(4*(D : ℝ))) :
    (floorMul α n).Coprime D := by
  have hDR : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have he : Int.fract ((2+α/D)*n) = Int.fract (α*n/D) := by
    have hh : (2+α/D)*n = α*n/D + ((2*n : ℕ) : ℝ) := by push_cast; ring
    rw [hh, Int.fract_add_natCast]
  rw [he] at hlo hhi
  apply floor_coprime_of_fract_div_mem (by positivity) D hD
  · have hh : 1/(D : ℝ) < 5/(4*(D : ℝ)) := by
      apply (div_lt_div_iff₀ hDR (by positivity)).mpr
      nlinarith only [hDR]
    exact hh.trans_le hlo
  · have hh : 7/(4*(D : ℝ)) < 2/(D : ℝ) := by
      apply (div_lt_div_iff₀ (by positivity) hDR).mpr
      nlinarith only [hDR]
    exact hhi.trans hh

lemma coprime_arc_margins {D v : ℕ} (hD : 2 ≤ D) (hDv : D ≤ v) :
    5/(4*(D : ℝ)) ≤ 7/(4*(D : ℝ)) ∧
      1/(v : ℝ)^3 ≤ 5/(4*(D : ℝ)) ∧
      1/(v : ℝ)^3 ≤ 1-7/(4*(D : ℝ)) := by
  have hDR : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hvR : (2 : ℝ) ≤ v := by exact_mod_cast hD.trans hDv
  have hDvR : (D : ℝ) ≤ v := Nat.cast_le.mpr hDv
  have hD0 : (0 : ℝ) < D := by linarith
  have hv0 : (0 : ℝ) < v := by linarith
  have hvc : (v : ℝ) ≤ (v : ℝ)^3 := by
    nlinarith only [hvR, sq_nonneg ((v : ℝ)-1)]
  have hve : (8 : ℝ) ≤ (v : ℝ)^3 := by
    have hh := mul_nonneg (show 0 ≤ (v : ℝ)-2 by linarith only [hvR])
      (show 0 ≤ (v : ℝ)^2+2*v+4 by positivity)
    nlinarith only [hh]
  refine ⟨div_le_div_of_nonneg_right (by norm_num) (by positivity), ?_, ?_⟩
  · calc
      _ ≤ 1/(D : ℝ) := one_div_le_one_div_of_le hD0 (hDvR.trans hvc)
      _ ≤ 5/(4*(D : ℝ)) := by
        apply (div_le_div_iff₀ hD0 (by positivity)).mpr
        nlinarith only [hD0]
  · have hh : 7/(4*(D : ℝ)) ≤ 7/8 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith only [hDR]
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) hve
    linarith only [hh, hi]

/-- A lower bound under a uniform arc estimate and an explicit error budget.
The prime-power contribution has already been removed from the input. -/
lemma coprimePrimeWeight_lower_of_arc {α E : ℝ} (hα : 0 ≤ α) {N v : ℕ}
    (hv : 2 ≤ v) (hθ : (N : ℝ)/2 ≤ Chebyshev.theta N)
    (hbudget : E + (Chebyshev.psi N - Chebyshev.theta N) ≤ (N : ℝ)/(8*v))
    (harc : ∀ D : ℕ, 2 ≤ D → D ≤ v →
      |mangoldtArcSum (2+α/D) 0 (5/(4*D)) (7/(4*D)) N -
        (1/(2*D))*Chebyshev.psi N| ≤ E)
    {D : ℕ} (hD : 0 < D) (hDv : D ≤ v) :
    (N : ℝ)/(8*D) ≤ coprimePrimeWeight α D N := by
  by_cases hD1 : D = 1
  · subst D
    rw [coprimePrimeWeight_one]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    norm_num only [Nat.cast_one, mul_one]
    linarith only [hθ, hN0]
  have hD2 : 2 ≤ D := by omega
  have hDR : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hvR : (0 : ℝ) < v := Nat.cast_pos.mpr (by omega)
  have hpp := Chebyshev.theta_le_psi (N : ℝ)
  have hψ : (N : ℝ)/2 ≤ Chebyshev.psi N := hθ.trans hpp
  have he := harc D hD2 hDv
  have hw : 7/(4*(D : ℝ))-5/(4*(D : ℝ)) = 1/(2*D) := by ring
  have hc := arc_le_coprimePrimeWeight_add_prime_powers α (2+α/D) 0
    (5/(4*D)) (7/(4*D)) D N
    (by
      intro n hn hlo hhi
      simp only [add_zero] at hlo hhi
      exact coprime_arc α hα hD n hlo hhi)
  have hb : E + (Chebyshev.psi N - Chebyshev.theta N) ≤ (N : ℝ)/(8*D) := by
    apply hbudget.trans
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hDv) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hψ (show 0 ≤ 1/(2*(D : ℝ)) by positivity)
  have hl := (abs_le.mp he).1
  have hid : 1/(2*(D : ℝ))*((N : ℝ)/2) = 2*((N : ℝ)/(8*D)) := by ring
  rw [hid] at hm
  linarith only [hl, hc, hb, hm]

lemma root64_le_self (u : ℕ) : root64 u ≤ u :=
  (Nat.le_self_pow (by decide : 64 ≠ 0) (root64 u)).trans
    ((le_root64_iff (root64 u) u).mp le_rfl)

lemma sixth_scale_primePower_tendsto :
    Tendsto (fun u : ℕ => (root64 u : ℝ) *
      (Chebyshev.psi (u^6 : ℕ) - Chebyshev.theta (u^6 : ℕ)) / (u : ℝ)^6)
      atTop (𝓝 0) := by
  let C : ℝ := Real.log 4 + 12
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlim : Tendsto (fun u : ℕ => C/(u : ℝ)^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [] with u
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (sub_nonneg.mpr (Chebyshev.theta_le_psi _))) (by positivity)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with u hu
    have huR : (0 : ℝ) < u := by exact_mod_cast hu
    have hN : (1 : ℝ) ≤ (u^6 : ℕ) := by
      exact_mod_cast Nat.one_le_pow 6 u hu
    have he := psi_sub_theta_le_sqrt hN
    have hs : Real.sqrt ((u^6 : ℕ) : ℝ) = (u : ℝ)^3 := by
      rw [Nat.cast_pow, show (u : ℝ)^6 = ((u : ℝ)^3)^2 by ring, Real.sqrt_sq (by positivity)]
    rw [hs] at he
    change _ ≤ C*(u : ℝ)^3 at he
    have hv : (root64 u : ℝ) ≤ u := Nat.cast_le.mpr (root64_le_self u)
    calc
      _ ≤ (root64 u : ℝ)*(C*(u : ℝ)^3)/(u : ℝ)^6 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)) (by positivity)
      _ ≤ (u : ℝ)*(C*(u : ℝ)^3)/(u : ℝ)^6 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv (by positivity)) (by positivity)
      _ = C/(u : ℝ)^2 := by field_simp

lemma eventually_coprime_prime_budget :
    ∀ᶠ u : ℕ in atTop,
      ((u^6 : ℕ) : ℝ)/2 ≤ Chebyshev.theta (u^6 : ℕ) ∧
      scaledRowError 1 u (root64 u) +
        (Chebyshev.psi (u^6 : ℕ) - Chebyshev.theta (u^6 : ℕ)) ≤
          ((u^6 : ℕ) : ℝ)/(8*root64 u) := by
  have hscale : Tendsto (fun u : ℕ => ((u^6 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_pow_atTop (by decide : 6 ≠ 0))
  have htheta := theta_div_self_tendsto.comp hscale
  have hE := summed_scaledRowError_tendsto 1 0
  simp only [pow_zero, mul_one] at hE
  have htotal : Tendsto (fun u : ℕ => (root64 u : ℝ) *
      (scaledRowError 1 u (root64 u) +
        (Chebyshev.psi (u^6 : ℕ) - Chebyshev.theta (u^6 : ℕ)))/(u : ℝ)^6)
      atTop (𝓝 0) := by
    simpa only [mul_add, add_div, add_zero] using hE.add sixth_scale_primePower_tendsto
  filter_upwards [(tendsto_order.mp htheta).1 (1/2) (by norm_num),
    (tendsto_order.mp htotal).2 (1/8) (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with u htheta htotal hu
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hN : (0 : ℝ) < (u^6 : ℕ) := by exact_mod_cast Nat.pow_pos hu (n := 6)
  have hv : (0 : ℝ) < root64 u := Nat.cast_pos.mpr (root64_bounds hu).1
  refine ⟨?_, ?_⟩
  · have hh := (lt_div_iff₀ hN).mp htheta
    linarith only [hh]
  · have hh := (div_lt_iff₀ (show 0 < (u : ℝ)^6 by positivity)).mp htotal
    apply (le_div_iff₀ (show 0 < 8*(root64 u : ℝ) by positivity)).mpr
    push_cast at hh ⊢
    nlinarith only [hh]

/-- At common scales, every modulus up to a growing power root can be avoided
by many genuine prime inputs. This is not a prime-output lower bound. -/
theorem exists_growing_coprime_prime_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (B : ℕ) :
    ∃ u : ℕ, B < u ∧ 2048 ≤ root64 u ∧
      ∀ D : ℕ, 0 < D → D ≤ root64 u →
        (u : ℝ)^6/(8*D) ≤ coprimePrimeWeight α D (u^6) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (eventually_coprime_prime_budget.and (root64_tendsto.eventually_ge_atTop 2048))
  let A := max T (B+1)
  obtain ⟨r, hr, hden⟩ := Erdos972RationalRoute.exists_good_approximant_large_den hα hI (A^4)
  let u := Nat.sqrt (Nat.sqrt r.den)
  have hAu : A ≤ u := (le_fourth_root_iff A r.den).mpr hden.le
  have hTu : T ≤ u := (le_max_left T (B+1)).trans hAu
  have hBu : B < u := by have := (le_max_right T (B+1)).trans hAu; omega
  obtain ⟨hu, hlo, hhi⟩ := fourth_root_bounds r.pos
  change 0 < u at hu
  change u^4 ≤ r.den at hlo
  change r.den ≤ 16*u^4 at hhi
  obtain ⟨⟨htheta, hbudget⟩, hv⟩ := hT u hTu
  have hv0 : 0 < root64 u := (root64_bounds hu).1
  have hv2 : 2 ≤ root64 u := by omega
  refine ⟨u, hBu, hv, ?_⟩
  intro D hD hDv
  have hc := coprimePrimeWeight_lower_of_arc (show 0 ≤ α by linarith) hv2 htheta hbudget
    (fun e he hev => ?_) hD hDv
  · simpa only [Nat.cast_pow] using hc
  obtain ⟨hab, ha, hb⟩ := coprime_arc_margins he hev
  have hh := scaled_arc_prefix_bound (show 0 ≤ α by linarith) r hr.le 1 u (root64 u) (root64 u)
    (by norm_num) hv0 le_rfl (by simpa using hv) (root64_bounds hu).2.1
    (by simpa using hlo) (by simpa using hhi)
    (5/(4*e)) (7/(4*e)) 0 hab ha hb e (u^6) (by omega) hev le_rfl
  have hw : 7/(4*(e : ℝ))-5/(4*(e : ℝ)) = 1/(2*e) := by ring
  simpa only [hw] using hh

#print axioms exists_growing_coprime_prime_scale

end Erdos972GrowingCoprimeCandidates
