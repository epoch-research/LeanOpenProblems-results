import Submission.DirectRowApproximation
import Submission.ChebyshevRowMean

/-! Power-root growing families of Beatty rows with uniform prefix errors.
These are still one-prime estimates, not bounds for the remaining Type-II sum. -/
namespace Erdos972PolynomialRowScales

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972ExponentialSum Erdos972PrimeRotation Erdos972RootScaleArc Erdos972WeightedPrimeRotation
open Erdos972DirectRowApproximation Erdos972ChebyshevRowMean Erdos972BeattyRows Erdos972BeattyRowScales

set_option maxHeartbeats 1000000

def root64 (u : ℕ) := Nat.sqrt (root32 u)

lemma le_root64_iff (v u : ℕ) : v ≤ root64 u ↔ v^64 ≤ u := by
  rw [root64, Nat.le_sqrt', le_root32_iff]
  norm_num only [← pow_mul]

lemma root64_bounds {u : ℕ} (hu : 0 < u) :
    0 < root64 u ∧ (root64 u)^64 ≤ u ∧ u ≤ 2^64*(root64 u)^64 := by
  have hv : 0 < root64 u := by
    have hh : 1 ≤ root64 u := (le_root64_iff 1 u).mpr (by simpa using hu)
    omega
  have hlo := (le_root64_iff (root64 u) u).mp le_rfl
  have hhi : u < (root64 u+1)^64 := by
    apply Nat.lt_of_not_ge
    intro hh
    have := (le_root64_iff (root64 u+1) u).mpr hh
    omega
  refine ⟨hv, hlo, hhi.le.trans ?_⟩
  calc
    _ ≤ (2*root64 u)^64 := Nat.pow_le_pow_left (by omega) 64
    _ = _ := by ring

lemma root64_tendsto : Tendsto root64 atTop atTop := by
  refine tendsto_atTop.2 (fun B => eventually_atTop.2 ⟨B^64, fun u hu => ?_⟩)
  exact (le_root64_iff B u).mpr hu

lemma positive_good_approximant_large_den {θ : ℝ} (hθ : 0 < θ) (hI : Irrational θ) (B : ℕ) :
    ∃ r : ℚ, B < r.den ∧ |θ-r| ≤ 1/(r.den : ℝ)^2 := by
  have hθ' : 1 < θ+2 := by linarith
  have hI' : Irrational (θ+2) := by simpa using hI.add_natCast 2
  obtain ⟨r, hr, hden⟩ := Erdos972RationalRoute.exists_good_approximant_large_den hθ' hI' B
  refine ⟨r-2, ?_, ?_⟩
  · simpa only [Rat.sub_ofNat_den] using hden
  · rw [Rat.sub_ofNat_den]
    have he : θ-(r-2 : ℚ) = θ+2-r := by push_cast; ring
    rw [he]
    exact hr.le

noncomputable def polynomialRowError (u v : ℕ) : ℝ :=
  (28+rotationConstant 256)*(1+Real.log u)^5*(u : ℝ)^6/(v : ℝ)^3

lemma polynomial_row_majorant {u v M : ℕ} (hu : 0 < u) (hv : 0 < v) (hMv : M ≤ v)
    (hvu : v^64 ≤ u) (X : ℕ) (hX : X ≤ u^6) :
    (2*(1/(v : ℝ)^3)+1/(v^9 : ℕ)+4/((4*(1/(v : ℝ)^3))^2*(v^9 : ℕ)))*Chebyshev.psi X+
      (v^9 : ℕ)*(rotationConstant (256*(v^9)*M)*(1+Real.log u)^5*(u : ℝ)^5*Real.sqrt u) ≤
        polynomialRowError u v := by
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
  have hc : rotationConstant (256*(v^9)*M) ≤ rotationConstant 256*(v : ℝ)^20 := by
    by_cases hM : M = 0
    · subst M
      have hbase : rotationConstant 0 ≤ rotationConstant 256 := by
        unfold rotationConstant
        norm_num
        nlinarith [Real.exp_pos (2*Real.pi)]
      exact hbase.trans (le_mul_of_one_le_right (rotationConstant_pos 256).le (one_le_pow₀ hv1))
    · have hh := rotationConstant_mul_le 256 (v^9*M) (by positivity)
      have hp : ((v^9*M : ℕ) : ℝ)^2 ≤ (v : ℝ)^20 := by
        have hmr : (M : ℝ) ≤ v := Nat.cast_le.mpr hMv
        push_cast
        calc
          _ ≤ ((v : ℝ)^9*v)^2 := by gcongr
          _ = _ := by ring
      calc
        _ = rotationConstant (256*(v^9*M)) := by congr 1; ring
        _ ≤ rotationConstant 256*(((v^9*M : ℕ) : ℝ)^2) := hh
        _ ≤ _ := mul_le_mul_of_nonneg_left hp (rotationConstant_pos 256).le
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
  have hsecond : (v^9 : ℕ)*(rotationConstant (256*(v^9)*M)*(1+Real.log u)^5*(u : ℝ)^5*Real.sqrt u) ≤
      rotationConstant 256*(1+Real.log u)^5*(u : ℝ)^6/(v : ℝ)^3 := by
    calc
      _ ≤ (v : ℝ)^9*((rotationConstant 256*(v : ℝ)^20)*(1+Real.log u)^5*(u : ℝ)^5*Real.sqrt u) := by
        push_cast
        gcongr
      _ = (rotationConstant 256*(1+Real.log u)^5)*((v : ℝ)^29*(u : ℝ)^5*Real.sqrt u) := by ring
      _ ≤ (rotationConstant 256*(1+Real.log u)^5)*((u : ℝ)^6/(v : ℝ)^3) :=
        mul_le_mul_of_nonneg_left hpower (by positivity [rotationConstant_pos 256])
      _ = _ := by ring
  calc
    _ ≤ 28*(1+Real.log u)^5*(u : ℝ)^6/(v : ℝ)^3 +
        rotationConstant 256*(1+Real.log u)^5*(u : ℝ)^6/(v : ℝ)^3 := add_le_add hfirst hsecond
    _ = _ := by unfold polynomialRowError; ring

/-- Uniform arc-prefix error for polynomially many reciprocal rows. -/
theorem polynomial_arc_prefix_bound {θ : ℝ} (hθ : 0 ≤ θ)
    (r : ℚ) (hr : |θ-r| ≤ 1/(r.den : ℝ)^2)
    (u v M : ℕ) (hM : 0 < M) (hMv : M ≤ v) (hv : 2048 ≤ v)
    (hvu : v^64 ≤ u) (hlo : u^4 ≤ r.den) (hhi : r.den ≤ 16*u^4)
    (a b t : ℝ) (hab : a ≤ b) (ha : 1/(v : ℝ)^3 ≤ a) (hb : 1/(v : ℝ)^3 ≤ 1-b)
    (m X : ℕ) (hm : 0 < m) (hmM : m ≤ M) (hX : X ≤ u^6) :
    |mangoldtArcSum (2+θ/m) t a b X-(b-a)*Chebyshev.psi X| ≤ polynomialRowError u v := by
  have hv0 : 0 < v := by omega
  have hu : 0 < u := (Nat.pow_pos hv0).trans_le hvu
  have helig : 2048*(v^9)*M ≤ u := by
    calc
      _ ≤ v*(v^9)*v := Nat.mul_le_mul (Nat.mul_le_mul_right _ hv) hMv
      _ = v^11 := by ring
      _ ≤ v^64 := Nat.pow_le_pow_right hv0 (by norm_num)
      _ ≤ u := hvu
  letI : NeZero (v^9) := ⟨by positivity⟩
  have hh := mangoldt_arc_discrepancy (2+θ/m) t X (H := v^9) a b (1/(v : ℝ)^3)
    (rotationConstant (256*(v^9)*M)*(1+Real.log u)^5*(u : ℝ)^5*Real.sqrt u)
    hab (by positivity) ha hb
    (by positivity [rotationConstant_pos (256*(v^9)*M), Real.log_natCast_nonneg u])
    (fun h hh hhH => reciprocal_rows_prefix_bound hθ r hr u M (v^9) hM (by positivity) helig hlo hhi
      m h X hm hmM hh hhH hX)
  exact hh.trans (polynomial_row_majorant hu hv0 hMv hvu X hX)

/-- Arbitrarily large scales with `v` comparable to the sixty-fourth root of
`u` control every row `m ≤ v`, uniformly over all prime-output prefixes. -/
theorem exists_polynomial_beatty_arc_scale_data {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ (u v : ℕ) (r : ℚ), B < u ∧ 2048 ≤ v ∧ v^64 ≤ u ∧ u ≤ 2^64*v^64 ∧ v = root64 u ∧
      |1/α-r| ≤ 1/(r.den : ℝ)^2 ∧ u^4 ≤ r.den ∧ r.den ≤ 16*u^4 ∧
      ∀ m : ℕ, 0 < m → m ≤ v → ∀ X : ℕ, X ≤ u^6 →
        |mangoldtArcSum (1/(α*m)) (-rowArcLeft (α*m)) (rowArcLeft (α*m)) (1-rowArcLeft (α*m)) X-
          (1/(α*m))*Chebyshev.psi X| ≤ polynomialRowError u v := by
  have hα0 : 0 < α := by linarith
  have hθ : 0 < 1/α := by positivity
  have hθI : Irrational (1/α) := by simpa only [one_div] using hI.inv
  have ha := (rowArcLeft_bounds hα).1
  let W := max 2048 (⌈1/rowArcLeft α⌉₊)
  let C := max (B+1) (W^64)
  obtain ⟨r, hden, hr⟩ := positive_good_approximant_large_den hθ hθI (C^4)
  let u := Nat.sqrt (Nat.sqrt r.den)
  have hCu : C ≤ u := (le_fourth_root_iff C r.den).mpr hden.le
  obtain ⟨hu, hlo, hhi⟩ := fourth_root_bounds r.pos
  change 0 < u at hu
  let v := root64 u
  obtain ⟨hv0, hvu, huv⟩ := root64_bounds hu
  have hWv : W ≤ v := (le_root64_iff W u).mpr ((le_max_right _ _).trans hCu)
  have hv : 2048 ≤ v := (le_max_left _ _).trans hWv
  have hmargin : 1/(v : ℝ)^3 ≤ rowArcLeft α := by
    have hvR : (0 : ℝ) < v := Nat.cast_pos.mpr hv0
    have hlow : 1/rowArcLeft α ≤ (v : ℝ) := (Nat.le_ceil _).trans
      (Nat.cast_le.mpr ((le_max_right _ _).trans hWv))
    have hv3 : (v : ℝ) ≤ (v : ℝ)^3 := by exact_mod_cast Nat.le_self_pow (by norm_num : 3 ≠ 0) v
    apply (one_div_le_one_div_of_le hvR hv3).trans
    exact (div_le_iff₀ hvR).mpr (by
      have hh := (div_le_iff₀ ha).mp hlow
      simpa only [mul_comm] using hh)
  refine ⟨u, v, r, ?_, hv, hvu, huv, rfl, hr, hlo, hhi, ?_⟩
  · have hh := (le_max_left (B+1) (W^64)).trans hCu
    omega
  · intro m hm hmv X hX
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hβ : 1 < α*m := by nlinarith only [hα, hmR]
    have harc := rowArcLeft_bounds hβ
    have hleft : 1/(v : ℝ)^3 ≤ rowArcLeft (α*m) :=
      hmargin.trans (rowArcLeft_mono hα0 (by nlinarith only [hα0, hmR]))
    have hh := polynomial_arc_prefix_bound hθ.le r hr u v v hv0 le_rfl hv hvu hlo hhi
      (rowArcLeft (α*m)) (1-rowArcLeft (α*m)) (-rowArcLeft (α*m)) (by linarith only [harc.2]) hleft (by linarith only [hleft])
      m X hm hmv hX
    rw [div_div, show (2 : ℝ) = (2 : ℕ) by norm_num, mangoldtArcSum_nat_add] at hh
    have hwidth : (1-rowArcLeft (α*m))-rowArcLeft (α*m) = 1/(α*m) := by unfold rowArcLeft; ring
    simpa only [hwidth] using hh

theorem exists_polynomial_beatty_arc_scale_root64 {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u v : ℕ, B < u ∧ 2048 ≤ v ∧ v^64 ≤ u ∧ u ≤ 2^64*v^64 ∧ v = root64 u ∧
      ∀ m : ℕ, 0 < m → m ≤ v → ∀ X : ℕ, X ≤ u^6 →
        |mangoldtArcSum (1/(α*m)) (-rowArcLeft (α*m)) (rowArcLeft (α*m)) (1-rowArcLeft (α*m)) X-
          (1/(α*m))*Chebyshev.psi X| ≤ polynomialRowError u v := by
  obtain ⟨u, v, r, hu, hv, hlo, hhi, heq, _, _, _, hrows⟩ := exists_polynomial_beatty_arc_scale_data hα hI B
  exact ⟨u, v, hu, hv, hlo, hhi, heq, hrows⟩

theorem exists_polynomial_beatty_arc_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α) (B : ℕ) :
    ∃ u v : ℕ, B < u ∧ 2048 ≤ v ∧ v^64 ≤ u ∧ u ≤ 2^64*v^64 ∧
      ∀ m : ℕ, 0 < m → m ≤ v → ∀ X : ℕ, X ≤ u^6 →
        |mangoldtArcSum (1/(α*m)) (-rowArcLeft (α*m)) (rowArcLeft (α*m)) (1-rowArcLeft (α*m)) X-
          (1/(α*m))*Chebyshev.psi X| ≤ polynomialRowError u v := by
  obtain ⟨u, v, hu, hv, hlo, hhi, _, hrows⟩ := exists_polynomial_beatty_arc_scale_root64 hα hI B
  exact ⟨u, v, hu, hv, hlo, hhi, hrows⟩

lemma root64_log_bound {u : ℕ} (hu : 0 < u) :
    1+Real.log u ≤ 65*(1+Real.log (root64 u)) := by
  obtain ⟨hv, _, hhi⟩ := root64_bounds hu
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hvR : (0 : ℝ) < root64 u := Nat.cast_pos.mpr hv
  have hhiR : (u : ℝ) ≤ (2 : ℝ)^64*(root64 u : ℝ)^64 := by exact_mod_cast hhi
  have hh := Real.log_le_log huR hhiR
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hlog2 : Real.log 2 ≤ 1 := by
    simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  linarith only [hh, hlog2, Real.log_natCast_nonneg (root64 u)]

lemma eventually_root64_log_small (C : ℝ) (hC : 0 < C) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, C*(1+Real.log u)^k ≤ ε*(root64 u : ℝ) := by
  let η := ε/(C*130^k)
  have hη : 0 < η := by dsimp [η]; positivity
  have hs : ∀ᶠ x : ℝ in atTop, ‖Real.log x^k‖ ≤ η*‖x‖ := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (k : ℝ) (by norm_num : (0:ℝ)<1)).bound hη
  have hv : Tendsto (fun u : ℕ => (root64 u : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp root64_tendsto
  filter_upwards [eventually_ge_atTop (1 : ℕ), hv.eventually hs,
    hv.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 1)] with u hu hsmall hlog
  have hl0 : 0 ≤ Real.log (root64 u) := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hl0 k), Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (root64 u))] at hsmall
  have hb : 1+Real.log u ≤ 130*Real.log (root64 u) := by
    linarith only [root64_log_bound hu, hlog]
  calc
    _ ≤ C*(130*Real.log (root64 u))^k := by gcongr
    _ = C*130^k*Real.log (root64 u)^k := by ring
    _ ≤ C*130^k*(η*(root64 u : ℝ)) := by gcongr
    _ = _ := by dsimp [η]; field_simp

lemma root64_log_div_tendsto (C : ℝ) (hC : 0 < C) (k : ℕ) :
    Tendsto (fun u : ℕ => C*(1+Real.log u)^k/(root64 u : ℝ)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_root64_log_small C hC k (show 0 < ε/2 by positivity),
    eventually_ge_atTop (1 : ℕ)] with u hu hu1
  have hv0 : (0 : ℝ) < root64 u := Nat.cast_pos.mpr (root64_bounds hu1).1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity [Real.log_natCast_nonneg u])]
  apply (div_lt_iff₀ hv0).mpr
  nlinarith only [hu, hε, hv0]

/-- Even the sum of one error per moving row, with any fixed logarithmic
weight, is sublinear at these scales. -/
theorem summed_polynomialRowError_tendsto (k : ℕ) :
    Tendsto (fun u : ℕ => (root64 u : ℝ)*(1+Real.log u)^k*polynomialRowError u (root64 u)/(u : ℝ)^6)
      atTop (𝓝 0) := by
  let C := 28+rotationConstant 256
  have hC : 0 < C := by dsimp [C]; positivity [rotationConstant_pos 256]
  have hi : Tendsto (fun u : ℕ => 1/(root64 u : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp root64_tendsto)
  have hh := (root64_log_div_tendsto C hC (k+5)).mul hi
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with u hu
  have hu0 : (u : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hu)
  have hv0 : (root64 u : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (root64_bounds hu).1)
  unfold polynomialRowError
  rw [pow_add]
  dsimp [C]
  field_simp

#print axioms summed_polynomialRowError_tendsto

#print axioms polynomial_row_majorant
#print axioms polynomial_arc_prefix_bound
#print axioms exists_polynomial_beatty_arc_scale

end Erdos972PolynomialRowScales
