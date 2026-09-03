import Submission.InverseGoodApproximation

/-! One-prime rotation bounds with a fixed denominator-comparison loss. -/
namespace Erdos972ScaledPrimeRows

open Finset ArithmeticFunction
open Erdos972PrimeRotation Erdos972PrefixPrimeRotation Erdos972ExponentialSum Erdos972VaughanSums
open Erdos972DirectRowApproximation Erdos972WeightedPrimeRotation Erdos972ChebyshevRowMean

set_option maxHeartbeats 1000000

theorem scaled_rows_prefix_bound {θ : ℝ} (hθ : 0 ≤ θ)
    (r : ℚ) (hr : |θ-r| ≤ 1/(r.den : ℝ)^2)
    (K u M H : ℕ) (hK : 0 < K) (hM : 0 < M) (hH : 0 < H) (hu : 2048*K*H*M ≤ u)
    (hlo : u^4 ≤ K*r.den) (hhi : r.den ≤ 16*K*u^4)
    (m h X : ℕ) (hm : 0 < m) (hmM : m ≤ M) (hh : 0 < h) (hhH : h ≤ H) (hX : X ≤ u^6) :
    ‖expSum vonMangoldt ((h : ℝ)*(2+θ/m)) X‖ ≤
      rotationConstant (256*K*H*M)*(1+Real.log u)^5*(u : ℝ)^5*Real.sqrt u := by
  obtain ⟨s, hslo, hshi, hsapprox⟩ := reciprocal_harmonic_approximant r hr m h H hm hh hhH
  have hspos : (0 : ℝ) < s := by
    have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hd1 : (1 : ℝ) ≤ s.den := by exact_mod_cast s.pos
    have herr : |(h : ℝ)*(2+θ/m)-s| ≤ 1 := hsapprox.trans
      ((div_le_one (by positivity)).mpr (by nlinarith))
    have hfreq : 2 ≤ (h : ℝ)*(2+θ/m) := by
      have hh0 : 0 ≤ θ/(m : ℝ) := by positivity
      nlinarith
    linarith [(abs_le.mp herr).2]
  have hrep := nonneg_rat_eq_natAbs_div s (by exact_mod_cast hspos.le)
  have hlow : u^4 ≤ (256*K*H*M)*s.den := by
    have hh := Nat.mul_le_mul_left K hslo
    have hHm : 4*K*H ≤ 256*K*H*M := by
      calc
        _ ≤ 256*K*H := Nat.mul_le_mul_right H (Nat.mul_le_mul_right K (by norm_num))
        _ ≤ _ := Nat.le_mul_of_pos_right _ hM
    have hh' := Nat.mul_le_mul_right s.den hHm
    nlinarith only [hlo, hh, hh']
  have hhigh : s.den ≤ (256*K*H*M)*u^4 := by
    calc
      _ ≤ 16*H*m*r.den := hshi
      _ ≤ 16*H*M*(16*K*u^4) := by gcongr
      _ = _ := by ring
  letI : NeZero s.den := ⟨s.den_ne_zero⟩
  exact expSum_sixth_scale_prefix_bound s.num.natAbs s.reduced ((h : ℝ)*(2+θ/m))
    (by simpa only [← hrep] using hsapprox) u (256*K*H*M) (by positivity) (by convert hu using 1 <;> ring) hlow hhigh X hX

noncomputable def scaledRowError (K u v : ℕ) : ℝ :=
  (28+rotationConstant (256*K))*(1+Real.log u)^5*(u : ℝ)^6/(v : ℝ)^3

lemma scaled_row_majorant (K : ℕ) {u v M : ℕ} (hu : 0 < u) (hv : 0 < v) (hM : 0 < M) (hMv : M ≤ v)
    (hvu : v^64 ≤ u) (X : ℕ) (hX : X ≤ u^6) :
    (2*(1/(v : ℝ)^3)+1/(v^9 : ℕ)+4/((4*(1/(v : ℝ)^3))^2*(v^9 : ℕ)))*Chebyshev.psi X+
      (v^9 : ℕ)*(rotationConstant (256*K*(v^9)*M)*(1+Real.log u)^5*(u : ℝ)^5*Real.sqrt u) ≤
        scaledRowError K u v := by
  have hvR : (0 : ℝ) < v := Nat.cast_pos.mpr hv
  have hv1 : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hS : 1 ≤ 1+Real.log u := by linarith [Real.log_natCast_nonneg u]
  have hcoef : 2*(1/(v : ℝ)^3)+1/(v^9 : ℕ)+4/((4*(1/(v : ℝ)^3))^2*(v^9 : ℕ)) ≤ 4/(v : ℝ)^3 := by
    push_cast
    field_simp
    have hh := one_le_pow₀ hv1 (n := 6)
    nlinarith
  have hpsi : Chebyshev.psi X ≤ 7*(u : ℝ)^6 := by
    have hXr : (X : ℝ) ≤ (u : ℝ)^6 := by exact_mod_cast hX
    exact (psi_le_seven_mul (Nat.cast_nonneg X)).trans (by nlinarith)
  have hfirst : (2*(1/(v : ℝ)^3)+1/(v^9 : ℕ)+4/((4*(1/(v : ℝ)^3))^2*(v^9 : ℕ)))*Chebyshev.psi X ≤
      28*(1+Real.log u)^5*(u : ℝ)^6/(v : ℝ)^3 := by
    calc
      _ ≤ (4/(v : ℝ)^3)*(7*(u : ℝ)^6) := by gcongr; exact Chebyshev.psi_nonneg _
      _ ≤ (4/(v : ℝ)^3)*(7*(u : ℝ)^6)*(1+Real.log u)^5 :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hS)
      _ = _ := by ring
  have hc : rotationConstant (256*K*(v^9)*M) ≤ rotationConstant (256*K)*(v : ℝ)^20 := by
    have hh := rotationConstant_mul_le (256*K) (v^9*M) (by positivity)
    have hp : ((v^9*M : ℕ) : ℝ)^2 ≤ (v : ℝ)^20 := by
      have hmr : (M : ℝ) ≤ v := Nat.cast_le.mpr hMv
      push_cast
      calc
        _ ≤ ((v : ℝ)^9*v)^2 := by gcongr
        _ = _ := by ring
    calc
      _ = rotationConstant ((256*K)*(v^9*M)) := by congr 1; ring
      _ ≤ rotationConstant (256*K)*(((v^9*M : ℕ) : ℝ)^2) := hh
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (rotationConstant_pos (256*K)).le
  have hvsqrt : (v : ℝ)^32 ≤ Real.sqrt u := by
    apply (Real.le_sqrt (by positivity) huR.le).mpr
    have hh : (v : ℝ)^64 ≤ u := by exact_mod_cast hvu
    convert hh using 1 <;> ring
  have hpower : (v : ℝ)^29*(u : ℝ)^5*Real.sqrt u ≤ (u : ℝ)^6/(v : ℝ)^3 := by
    apply (le_div_iff₀ (pow_pos hvR 3)).mpr
    calc
      _ = (v : ℝ)^32*(u : ℝ)^5*Real.sqrt u := by ring
      _ ≤ Real.sqrt u*(u : ℝ)^5*Real.sqrt u := by gcongr
      _ = (u : ℝ)^5*(Real.sqrt u)^2 := by ring
      _ = (u : ℝ)^6 := by rw [Real.sq_sqrt huR.le]; ring
  have hsecond : (v^9 : ℕ)*(rotationConstant (256*K*(v^9)*M)*(1+Real.log u)^5*(u : ℝ)^5*Real.sqrt u) ≤
      rotationConstant (256*K)*(1+Real.log u)^5*(u : ℝ)^6/(v : ℝ)^3 := by
    calc
      _ ≤ (v : ℝ)^9*((rotationConstant (256*K)*(v : ℝ)^20)*(1+Real.log u)^5*(u : ℝ)^5*Real.sqrt u) := by
        push_cast
        gcongr
      _ = (rotationConstant (256*K)*(1+Real.log u)^5)*((v : ℝ)^29*(u : ℝ)^5*Real.sqrt u) := by ring
      _ ≤ (rotationConstant (256*K)*(1+Real.log u)^5)*((u : ℝ)^6/(v : ℝ)^3) :=
        mul_le_mul_of_nonneg_left hpower (by positivity [rotationConstant_pos (256*K)])
      _ = _ := by ring
  calc
    _ ≤ 28*(1+Real.log u)^5*(u : ℝ)^6/(v : ℝ)^3 +
        rotationConstant (256*K)*(1+Real.log u)^5*(u : ℝ)^6/(v : ℝ)^3 := add_le_add hfirst hsecond
    _ = _ := by unfold scaledRowError; ring

/-- Uniform arc-prefix error for polynomially many reciprocal rows. -/
theorem scaled_arc_prefix_bound {θ : ℝ} (hθ : 0 ≤ θ)
    (r : ℚ) (hr : |θ-r| ≤ 1/(r.den : ℝ)^2)
    (K u v M : ℕ) (hK : 0 < K) (hM : 0 < M) (hMv : M ≤ v) (hv : 2048*K ≤ v)
    (hvu : v^64 ≤ u) (hlo : u^4 ≤ K*r.den) (hhi : r.den ≤ 16*K*u^4)
    (a b t : ℝ) (hab : a ≤ b) (ha : 1/(v : ℝ)^3 ≤ a) (hb : 1/(v : ℝ)^3 ≤ 1-b)
    (m X : ℕ) (hm : 0 < m) (hmM : m ≤ M) (hX : X ≤ u^6) :
    |mangoldtArcSum (2+θ/m) t a b X-(b-a)*Chebyshev.psi X| ≤ scaledRowError K u v := by
  have hv0 : 0 < v := (show 0 < 2048*K by positivity).trans_le hv
  have hu : 0 < u := (Nat.pow_pos hv0).trans_le hvu
  have helig : 2048*K*(v^9)*M ≤ u := by
    calc
      _ ≤ v*(v^9)*v := Nat.mul_le_mul (Nat.mul_le_mul_right _ hv) hMv
      _ = v^11 := by ring
      _ ≤ v^64 := Nat.pow_le_pow_right hv0 (by norm_num)
      _ ≤ u := hvu
  letI : NeZero (v^9) := ⟨by positivity⟩
  have hh := mangoldt_arc_discrepancy (2+θ/m) t X (H := v^9) a b (1/(v : ℝ)^3)
    (rotationConstant (256*K*(v^9)*M)*(1+Real.log u)^5*(u : ℝ)^5*Real.sqrt u)
    hab (by positivity) ha hb
    (by positivity [rotationConstant_pos (256*K*(v^9)*M), Real.log_natCast_nonneg u])
    (fun h hh hhH => scaled_rows_prefix_bound hθ r hr K u M (v^9) hK hM (by positivity) helig hlo hhi
      m h X hm hmM hh hhH hX)
  exact hh.trans (scaled_row_majorant K hu hv0 hM hMv hvu X hX)


#print axioms scaled_arc_prefix_bound

end Erdos972ScaledPrimeRows
