import Submission.WeightedPrimeRotation

/-! Growing Fourier cutoffs on selected rational scales. Quantitative
one-prime rotation discrepancy remains negligible after logarithmic weighting. -/
namespace Erdos972RootScaleArc

open Finset ArithmeticFunction Filter
open scoped Topology
open Erdos972ExponentialSum Erdos972VaughanSums Erdos972PrimeRotation
open Erdos972PrefixPrimeRotation Erdos972WeightedPrimeRotation

set_option maxHeartbeats 1000000

def root32 (u : ℕ) : ℕ := Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.sqrt u))))

lemma le_root32_iff (v u : ℕ) : v ≤ root32 u ↔ v^32 ≤ u := by
  unfold root32
  rw [Nat.le_sqrt', Nat.le_sqrt', Nat.le_sqrt', Nat.le_sqrt', Nat.le_sqrt']
  norm_num only [← pow_mul]

lemma root32_bounds {u : ℕ} (hu : 0 < u) :
    0 < root32 u ∧ (root32 u)^32 ≤ u ∧ u ≤ 2^32*(root32 u)^32 := by
  have hv : 0 < root32 u := by
    have : 1 ≤ root32 u := (le_root32_iff 1 u).mpr (by simpa using hu)
    omega
  have hlo := (le_root32_iff (root32 u) u).mp le_rfl
  have hhi : u < (root32 u + 1)^32 := by
    apply Nat.lt_of_not_ge
    intro hh
    have := (le_root32_iff (root32 u + 1) u).mpr hh
    omega
  refine ⟨hv, hlo, hhi.le.trans ?_⟩
  calc
    _ ≤ (2*root32 u)^32 := Nat.pow_le_pow_left (by omega) 32
    _ = _ := by ring

lemma root32_tendsto : Tendsto root32 atTop atTop := by
  refine tendsto_atTop.2 (fun B => eventually_atTop.2 ⟨B^32, fun u hu => ?_⟩)
  exact (le_root32_iff B u).mpr hu

lemma root32_log_bound {u : ℕ} (hu : 0 < u) :
    1 + Real.log u ≤ 33*(1 + Real.log (root32 u)) := by
  obtain ⟨hv, _, hhi⟩ := root32_bounds hu
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hvR : (0 : ℝ) < root32 u := Nat.cast_pos.mpr hv
  have hhiR : (u : ℝ) ≤ (2 : ℝ)^32*(root32 u : ℝ)^32 := by exact_mod_cast hhi
  have hh := Real.log_le_log huR hhiR
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  have hlog2 : Real.log 2 ≤ 1 := by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  linarith [Real.log_natCast_nonneg (root32 u)]

/-- Any fixed logarithmic power is dominated by the small auxiliary root. -/
lemma eventually_root32_log_small (C : ℝ) (hC : 0 < C) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ u : ℕ in atTop, C*(1+Real.log u)^k ≤ ε*(root32 u : ℝ) := by
  let η := ε/(C*66^k)
  have hη : 0 < η := by dsimp [η]; positivity
  have hs : ∀ᶠ x : ℝ in atTop, ‖Real.log x ^ k‖ ≤ η*‖x‖ := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (k : ℝ) (by norm_num : (0:ℝ)<1)).bound hη
  have hv : Tendsto (fun u : ℕ => (root32 u : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp root32_tendsto
  filter_upwards [eventually_ge_atTop (1 : ℕ), hv.eventually hs,
    hv.eventually (Real.tendsto_log_atTop.eventually_ge_atTop 1)] with u hu hsmall hlog
  have hl0 : 0 ≤ Real.log (root32 u) := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hl0 k), Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (root32 u))] at hsmall
  have hb : 1+Real.log u ≤ 66*Real.log (root32 u) := by
    have hh := root32_log_bound hu
    linarith
  calc
    _ ≤ C*(66*Real.log (root32 u))^k := by gcongr
    _ = C*66^k*Real.log (root32 u)^k := by ring
    _ ≤ C*66^k*(η*(root32 u : ℝ)) := by gcongr
    _ = _ := by dsimp [η]; field_simp

lemma growing_cutoff_eligible {u v D : ℕ} (hv : 0 < v) (hD : 512*D ≤ v)
    (hvu : v^32 ≤ u) : 512*(D*v^3) ≤ u := by
  calc
    _ = (512*D)*v^3 := by ring
    _ ≤ v*v^3 := Nat.mul_le_mul_right _ hD
    _ = v^4 := by ring
    _ ≤ v^32 := Nat.pow_le_pow_right hv (by norm_num)
    _ ≤ u := hvu

/-- Elementary majorants at the growing cutoff `H=v^3`, `δ=1/v`. -/
lemma growing_arc_majorant {u v D : ℕ} (hu : 0 < u) (hv : 0 < v) (hvu : v^32 ≤ u)
    (X : ℕ) (hX : X ≤ u^6) :
    (2*(1/(v : ℝ)) + 1/(v^3 : ℕ) + 4/((4*(1/(v : ℝ)))^2 * (v^3 : ℕ)))*Chebyshev.psi X +
      (v^3 : ℕ) * (rotationConstant (64*(D*v^3)) * (1+Real.log u)^5 * (u : ℝ)^5 * Real.sqrt u) ≤
      (28+rotationConstant (64*D))*(1+Real.log u)^5*(u : ℝ)^6/v := by
  have hvR : (0 : ℝ) < v := Nat.cast_pos.mpr hv
  have hv1 : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hS : 1 ≤ 1+Real.log u := by linarith [Real.log_natCast_nonneg u]
  have hcoef : 2*(1/(v : ℝ)) + 1/(v^3 : ℕ) + 4/((4*(1/(v : ℝ)))^2 * (v^3 : ℕ)) ≤ 4/v := by
    push_cast
    field_simp
    nlinarith [sq_nonneg (v : ℝ), mul_nonneg (show 0 ≤ (v : ℝ)-1 by linarith)
      (show 0 ≤ (v : ℝ)+1 by positivity)]
  have hpsi : Chebyshev.psi X ≤ 7*(u : ℝ)^6 := by
    have hh := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) X)
    have hlog4 : Real.log 4 ≤ 3 := by simpa only [show (4:ℝ)-1=3 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    have hXr : (X : ℝ) ≤ (u : ℝ)^6 := by exact_mod_cast hX
    nlinarith [Nat.cast_nonneg (α := ℝ) X]
  have hfirst : (2*(1/(v : ℝ)) + 1/(v^3 : ℕ) + 4/((4*(1/(v : ℝ)))^2 * (v^3 : ℕ)))*Chebyshev.psi X ≤
      28*(1+Real.log u)^5*(u : ℝ)^6/v := by
    calc
      _ ≤ (4/(v : ℝ)) * (7*(u : ℝ)^6) := by gcongr; exact Chebyshev.psi_nonneg _
      _ ≤ (4/(v : ℝ)) * (7*(u : ℝ)^6) * (1+Real.log u)^5 :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hS)
      _ = _ := by ring
  have hc : rotationConstant (64*(D*v^3)) ≤ rotationConstant (64*D)*(v : ℝ)^6 := by
    have hh := rotationConstant_mul_le (64*D) (v^3) (by positivity)
    convert hh using 1 <;> push_cast <;> congr 1 <;> ring
  have hvsqrt : (v : ℝ)^10 ≤ Real.sqrt u := by
    apply (Real.le_sqrt (by positivity) huR.le).mpr
    have hh : v^20 ≤ u := (Nat.pow_le_pow_right hv (by norm_num : 20 ≤ 32)).trans hvu
    have hhR : (v : ℝ)^20 ≤ u := by exact_mod_cast hh
    convert hhR using 1 <;> ring
  have hpower : (v : ℝ)^9 * (u : ℝ)^5 * Real.sqrt u ≤ (u : ℝ)^6/v := by
    apply (le_div_iff₀ hvR).mpr
    calc
      _ = (v : ℝ)^10 * (u : ℝ)^5 * Real.sqrt u := by ring
      _ ≤ Real.sqrt u * (u : ℝ)^5 * Real.sqrt u := by gcongr
      _ = (u : ℝ)^5 * (Real.sqrt u)^2 := by ring
      _ = (u : ℝ)^6 := by rw [Real.sq_sqrt huR.le]; ring
  have hsecond : (v^3 : ℕ) * (rotationConstant (64*(D*v^3)) * (1+Real.log u)^5 * (u : ℝ)^5 * Real.sqrt u) ≤
      rotationConstant (64*D)*(1+Real.log u)^5*(u : ℝ)^6/v := by
    calc
      _ ≤ (v : ℝ)^3 * ((rotationConstant (64*D)*(v : ℝ)^6) * (1+Real.log u)^5 * (u : ℝ)^5 * Real.sqrt u) := by
        push_cast
        gcongr
      _ = (rotationConstant (64*D)*(1+Real.log u)^5) * ((v : ℝ)^9*(u : ℝ)^5*Real.sqrt u) := by ring
      _ ≤ (rotationConstant (64*D)*(1+Real.log u)^5) * ((u : ℝ)^6/v) := by
        exact mul_le_mul_of_nonneg_left hpower (by positivity [rotationConstant_pos (64*D)])
      _ = _ := by ring
  calc
    _ ≤ 28*(1+Real.log u)^5*(u : ℝ)^6/v + rotationConstant (64*D)*(1+Real.log u)^5*(u : ℝ)^6/v :=
      add_le_add hfirst hsecond
    _ = _ := by ring

/-- A growing cutoff controls finitely many base multiples simultaneously,
with a power-root saving uniform over every shorter prime prefix. -/
theorem growing_arc_prefix_bound {θ : ℝ} (hθ : 1 < θ)
    (r : ℚ) (hr : |θ-r| ≤ 1/(r.den : ℝ)^2)
    (u D : ℕ) (hu : 0 < u) (hD : 0 < D) (hvD : 512*D ≤ root32 u)
    (hlo : u^4 ≤ r.den) (hhi : r.den ≤ 16*u^4)
    (a b t : ℝ) (hab : a ≤ b)
    (ha : 1/(root32 u : ℝ) ≤ a) (hb : 1/(root32 u : ℝ) ≤ 1-b)
    (m X : ℕ) (hm : 0 < m) (hmD : m ≤ D) (hX : X ≤ u^6) :
    |mangoldtArcSum ((m : ℝ)*θ) t a b X - (b-a)*Chebyshev.psi X| ≤
      (28+rotationConstant (64*D))*(1+Real.log u)^5*(u : ℝ)^6/(root32 u : ℝ) := by
  let v := root32 u
  obtain ⟨hv, hvu, _⟩ := root32_bounds hu
  letI : NeZero (v^3) := ⟨by dsimp [v]; positivity⟩
  have helig := growing_cutoff_eligible hv hvD hvu
  let E := rotationConstant (64*(D*v^3))*(1+Real.log u)^5*(u : ℝ)^5*Real.sqrt u
  have hE0 : 0 ≤ E := by dsimp [E]; positivity [rotationConstant_pos (64*(D*v^3)), Real.log_natCast_nonneg u]
  have hE (h : ℕ) (hh : 0 < h) (hhH : h ≤ v^3) :
      ‖expSum vonMangoldt ((h : ℝ)*((m : ℝ)*θ)) X‖ ≤ E := by
    have hhm : h*m ≤ D*v^3 := by nlinarith
    have he := simultaneous_prefix_bound hθ r hr u (D*v^3) (by positivity) helig hlo hhi
      (h*m) (by positivity) hhm X hX
    simpa only [E, Nat.cast_mul, mul_assoc] using he
  exact (mangoldt_arc_discrepancy ((m : ℝ)*θ) t X (H := v^3) a b (1/(v : ℝ)) E hab
    (by positivity) ha hb hE0 hE).trans (growing_arc_majorant hu hv hvu X hX)

/-- At arbitrarily large common scales, interval discrepancy is smaller than
any prescribed multiple of `u^6`, even after multiplication by any fixed
power of `1+log u`. The estimate is uniform over all shorter prefixes, all
translations, and finitely many integer multiples of the rotation. -/
theorem exists_log_weighted_uniform_arc_scale {θ : ℝ} (hθ : 1 < θ) (hI : Irrational θ)
    (D k : ℕ) (hD : 0 < D) (η : ℝ) (hη : 0 < η)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ u : ℕ, N < u ∧ ∀ m : ℕ, 0 < m → m ≤ D → ∀ a b : ℝ, a ≤ b → η ≤ a → η ≤ 1-b → ∀ t : ℝ, ∀ X : ℕ, X ≤ u^6 →
      |mangoldtArcSum ((m : ℝ)*θ) t a b X - (b-a)*Chebyshev.psi X| * (1+Real.log u)^k ≤ ε*(u : ℝ)^6 := by
  let C := 28+rotationConstant (64*D)
  have hC : 0 < C := by dsimp [C]; positivity [rotationConstant_pos (64*D)]
  have hv : Tendsto (fun u : ℕ => (root32 u : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp root32_tendsto
  have hinv : Tendsto (fun u : ℕ => 1/(root32 u : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hv
  have hgood : ∀ᶠ u : ℕ in atTop, 0 < u ∧ 512*D ≤ root32 u ∧
      1/(root32 u : ℝ) ≤ η ∧
      C*(1+Real.log u)^(k+5) ≤ ε*(root32 u : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), root32_tendsto.eventually (eventually_ge_atTop (512*D)),
      (tendsto_order.mp hinv).2 η hη,
      eventually_root32_log_small C hC (k+5) hε] with u hu hD' hη' hsmall
    exact ⟨hu, hD', hη'.le, hsmall⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp hgood
  let B := max T (N+1)
  obtain ⟨r, hr, hden⟩ := Erdos972RationalRoute.exists_good_approximant_large_den hθ hI (B^4)
  let u := Nat.sqrt (Nat.sqrt r.den)
  have hBu : B ≤ u := (le_fourth_root_iff B r.den).mpr hden.le
  have hTu : T ≤ u := (le_max_left T (N+1)).trans hBu
  have hNu : N < u := by have := (le_max_right T (N+1)).trans hBu; omega
  obtain ⟨hu, hvD, hη', hsmall⟩ := hT u hTu
  obtain ⟨_, hlo, hhi⟩ := fourth_root_bounds r.pos
  have hv0 : (0 : ℝ) < root32 u := Nat.cast_pos.mpr (root32_bounds hu).1
  refine ⟨u, hNu, ?_⟩
  intro m hm hmD a b hab ha hb t X hX
  have hbound := growing_arc_prefix_bound hθ r hr.le u D hu hD hvD hlo hhi a b t hab (hη'.trans ha) (hη'.trans hb) m X hm hmD hX
  calc
    _ ≤ (C*(1+Real.log u)^5*(u : ℝ)^6/(root32 u : ℝ))*(1+Real.log u)^k := by
      exact mul_le_mul_of_nonneg_right hbound (by positivity [Real.log_natCast_nonneg u])
    _ = (C*(1+Real.log u)^(k+5)/(root32 u : ℝ))*(u : ℝ)^6 := by rw [pow_add]; ring
    _ ≤ ε*(u : ℝ)^6 := by
      exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hv0).mpr hsmall) (by positivity)

/-- At arbitrarily large common scales, interval discrepancy is smaller than
any prescribed multiple of `u^6`, even after multiplication by any fixed
power of `1+log u`. The estimate is uniform over all shorter prefixes, all
translations, and finitely many integer multiples of the rotation. -/
theorem exists_log_weighted_common_arc_scale {θ : ℝ} (hθ : 1 < θ) (hI : Irrational θ)
    (D k : ℕ) (hD : 0 < D) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ u : ℕ, N < u ∧ ∀ m : ℕ, 0 < m → m ≤ D → ∀ t : ℝ, ∀ X : ℕ, X ≤ u^6 →
      |mangoldtArcSum ((m : ℝ)*θ) t a b X - (b-a)*Chebyshev.psi X| * (1+Real.log u)^k ≤ ε*(u : ℝ)^6 := by
  obtain ⟨u, hu, hh⟩ := exists_log_weighted_uniform_arc_scale hθ hI D k hD (min a (1-b))
    (lt_min ha (by linarith)) hε N
  refine ⟨u, hu, ?_⟩
  intro m hm hmD t X hX
  exact hh m hm hmD a b hab (min_le_left _ _) (min_le_right _ _) t X hX

#print axioms growing_arc_prefix_bound
#print axioms exists_log_weighted_common_arc_scale
#print axioms exists_log_weighted_uniform_arc_scale

#print axioms eventually_root32_log_small
#print axioms growing_arc_majorant

end Erdos972RootScaleArc
