import Submission.PrimeRotation

/-! Uniform-prefix versions of the one-prime exponential estimates. These
bounds do not estimate a sum with a second Mangoldt factor. -/
namespace Erdos972PrefixPrimeRotation

open Finset ArithmeticFunction Filter
open scoped Topology
open Erdos972ExponentialSum Erdos972VaughanSums Erdos972PrimeRotation

noncomputable def vaughanMajorant (q U X : ℕ) : ℝ :=
  4 * Real.log (X + 1) * q * (2 + Real.log q) +
    2 * Real.log (U * U) * q * (2 + Real.log q) + Chebyshev.psi U +
    (Nat.log 2 X + 1 : ℕ) *
      (Real.exp (2 * Real.pi) * (2 + Real.log (2 * X + 1)) ^ 4 *
        Real.sqrt (2 * (X : ℝ) * (2 * X / q + 4 * (X / U : ℕ) + q)))

lemma vaughanMajorant_mono (q U : ℕ) : Monotone (vaughanMajorant q U) := by
  intro X Y hXY
  have hXYr : (X : ℝ) ≤ Y := Nat.cast_le.mpr hXY
  have hlogq : 0 ≤ 2 + Real.log q := by linarith [Real.log_natCast_nonneg q]
  have hlogX : 0 ≤ 2 + Real.log (2 * (X : ℝ) + 1) := by
    have := Real.log_nonneg (show 1 ≤ 2 * (X : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) X])
    linarith
  have hlogY : 0 ≤ 2 + Real.log (2 * (Y : ℝ) + 1) := by
    have := Real.log_nonneg (show 1 ≤ 2 * (Y : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) Y])
    linarith
  have hJ : ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ (Nat.log 2 Y + 1 : ℕ) := by
    exact_mod_cast Nat.add_le_add_right (Nat.log_monotone hXY) 1
  have hD : ((X / U : ℕ) : ℝ) ≤ (Y / U : ℕ) := by
    exact_mod_cast Nat.div_le_div_right hXY
  unfold vaughanMajorant
  gcongr

/-- Every shorter prefix has the same rational-scale error bound. -/
theorem expSum_sixth_scale_prefix_bound {q : ℕ} [NeZero q]
    (a : ℕ) (ha : a.Coprime q) (θ : ℝ)
    (hθ : |θ - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (u K : ℕ) (hK : 0 < K) (hu : 8 * K ≤ u)
    (hlo : u ^ 4 ≤ K * q) (hhi : q ≤ K * u ^ 4)
    (X : ℕ) (hX : X ≤ u ^ 6) :
    ‖expSum vonMangoldt θ X‖ ≤
      rotationConstant K * (1 + Real.log u) ^ 5 * (u : ℝ) ^ 5 * Real.sqrt u := by
  have hu0 : 0 < u := lt_of_lt_of_le (by positivity : 0 < 8 * K) hu
  obtain ⟨hUq, hXq⟩ := sixth_scale_eligible hK hu hlo
  have hXq' : 2 * (X : ℝ) ≤ (q : ℝ) ^ 2 := by
    have : (X : ℝ) ≤ (u : ℝ) ^ 6 := by exact_mod_cast hX
    linarith
  have hb := vonMangoldt_expSum_bound a ha θ hθ u X hu0 hUq hXq'
  change ‖expSum vonMangoldt θ X‖ ≤ vaughanMajorant q u X at hb
  apply (hb.trans (vaughanMajorant_mono q u hX)).trans
  simpa only [vaughanMajorant, Nat.cast_pow] using sixth_scale_majorant u K hu0 hK hlo hhi

/-- One base rational approximation controls every frequency up to `H` and every
prefix up to `u^6`. The cutoff `H` may vary with the chosen rational scale. -/
theorem simultaneous_prefix_bound {θ : ℝ} (hθ : 1 < θ)
    (r : ℚ) (hr : |θ - r| ≤ 1 / (r.den : ℝ) ^ 2)
    (u H : ℕ) (hH : 0 < H) (hu : 512 * H ≤ u)
    (hlo : u ^ 4 ≤ r.den) (hhi : r.den ≤ 16 * u ^ 4) :
    ∀ h : ℕ, 0 < h → h ≤ H → ∀ X : ℕ, X ≤ u ^ 6 →
      ‖expSum vonMangoldt ((h : ℝ) * θ) X‖ ≤
        rotationConstant (64 * H) * (1 + Real.log u) ^ 5 * (u : ℝ) ^ 5 * Real.sqrt u := by
  intro h hh hhH X hX
  obtain ⟨s, hslo, hshi, hsapprox⟩ := simultaneous_approximant r hr h H hh hhH
  have hspos : (0 : ℝ) < s := by
    have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hd1 : (1 : ℝ) ≤ s.den := by exact_mod_cast s.pos
    have herr : |(h : ℝ) * θ - s| ≤ 1 := hsapprox.trans
      ((div_le_one (by positivity)).mpr (by nlinarith))
    have := (abs_le.mp herr).2
    nlinarith
  have hsrep := nonneg_rat_eq_natAbs_div s (by exact_mod_cast hspos.le)
  have hslow : u ^ 4 ≤ (64 * H) * s.den := by nlinarith
  have hshigh : s.den ≤ (64 * H) * u ^ 4 := by nlinarith
  letI : NeZero s.den := ⟨s.den_ne_zero⟩
  exact expSum_sixth_scale_prefix_bound s.num.natAbs s.reduced ((h : ℝ) * θ)
    (by simpa only [← hsrep] using hsapprox) u (64 * H) (by positivity)
    (by omega) hslow hshigh X hX

/-- Arbitrarily large simultaneous good scales with uniform control of all
prefixes, not just the sum at the endpoint. -/
theorem exists_common_prefix_scale {θ : ℝ} (hθ : 1 < θ) (hI : Irrational θ)
    (H : ℕ) (hH : 0 < H) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ u : ℕ, N < u ∧ ∀ h : ℕ, 0 < h → h ≤ H → ∀ X : ℕ, X ≤ u ^ 6 →
      ‖expSum vonMangoldt ((h : ℝ) * θ) X‖ ≤ ε * (u : ℝ) ^ 6 := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_rotation_majorant_small (64 * H) hε)
  let B := max T (max (512 * H) (N + 1))
  obtain ⟨r, hr, hden⟩ := Erdos972RationalRoute.exists_good_approximant_large_den hθ hI (B ^ 4)
  let u := Nat.sqrt (Nat.sqrt r.den)
  have hBu : B ≤ u := (le_fourth_root_iff B r.den).mpr hden.le
  have hu : 512 * H ≤ u := (le_trans (le_max_left _ _) (le_max_right T _)).trans hBu
  have hNu : N < u := by
    have := (le_trans (le_max_right _ _) (le_max_right T _)).trans hBu
    omega
  have hTu : T ≤ u := (le_max_left _ _).trans hBu
  obtain ⟨hu0, hulow, huhi⟩ := fourth_root_bounds r.pos
  refine ⟨u, hNu, ?_⟩
  intro h hh hhH X hX
  exact (simultaneous_prefix_bound hθ r hr.le u H hH hu hulow huhi h hh hhH X hX).trans (hT u hTu)

#print axioms expSum_sixth_scale_prefix_bound
#print axioms simultaneous_prefix_bound
#print axioms exists_common_prefix_scale

end Erdos972PrefixPrimeRotation
