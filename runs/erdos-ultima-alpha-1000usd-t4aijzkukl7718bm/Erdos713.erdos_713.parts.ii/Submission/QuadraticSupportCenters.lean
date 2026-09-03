import FormalConjecturesUtil
import Submission.QuadraticSupportTangents

/-! Quadratic supports near every large order. These statements concern
macroscopic order ratios, not bounded additive gaps between supports. -/
open Filter Asymptotics Finset
open scoped Topology
namespace Erdos713QuadraticSupportCenters
open Erdos713ExactCloneSaturation Erdos713QuadraticSupports
open Erdos713QuadraticSupportTangents
set_option maxHeartbeats 2000000

lemma support_center_limit {f : ℕ → ℕ} {α c : ℝ} (ha : 0 < α)
    (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    {n k : ℕ → ℕ} (hn : Tendsto n atTop atTop) (hk : Tendsto k atTop atTop)
    (hs : ∀ i, QuadSupport f (c*α/2*(k i : ℝ)^(α-2)) (n i)) :
    Tendsto (fun i => (n i : ℝ)/(k i : ℝ)) atTop (𝓝 1) := by
  let C := c*α/2
  have hC : 0 < C := by dsimp [C]; positivity
  have hp : 0 < 2-α := by linarith
  have hSlope := support_slope_limit h hn hs
  have hInv : Tendsto (fun i => (n i : ℝ)⁻¹) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.comp hn).inv_tendsto_atTop
  have hFac : Tendsto (fun i => C*(2-(n i : ℝ)⁻¹)) atTop (𝓝 (C*2)) := by
    simpa using (hInv.const_sub 2).const_mul C
  have hPower : Tendsto (fun i => ((n i : ℝ)/(k i : ℝ))^(2-α)) atTop (𝓝 1) := by
    have hh := hSlope.div hFac (by positivity : C*2 ≠ 0)
    have he : c*α/(C*2) = 1 := by dsimp [C]; field_simp
    rw [he] at hh
    apply hh.congr'
    filter_upwards [hn.eventually (eventually_gt_atTop (0 : ℕ)),
      hk.eventually (eventually_gt_atTop (0 : ℕ))] with i hni hki
    have hnR : (0 : ℝ) < n i := by exact_mod_cast hni
    have hkR : (0 : ℝ) < k i := by exact_mod_cast hki
    have hn1 : (1 : ℝ) ≤ n i := by exact_mod_cast hni
    have hFacNe : 2-(n i : ℝ)⁻¹ ≠ 0 := by
      have hi : (n i : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hnR).mpr hn1
      linarith
    change (C*(k i : ℝ)^(α-2)*(2*(n i : ℝ)-1)/(n i : ℝ)^(α-1))/
      (C*(2-(n i : ℝ)⁻¹)) = _
    rw [Real.div_rpow hnR.le hkR.le,Real.rpow_sub hkR,Real.rpow_sub hnR,
      Real.rpow_sub hnR,Real.rpow_sub hkR,Real.rpow_one,Real.rpow_two,Real.rpow_two]
    have hne2 : 2*(n i : ℝ)-1 ≠ 0 := by linarith
    field_simp [hC.ne',hFacNe,hne2,hnR.ne',hkR.ne',
      (Real.rpow_pos_of_pos hnR α).ne',(Real.rpow_pos_of_pos hkR α).ne']
  have hh := hPower.rpow_const (p := (2-α)⁻¹) (Or.inl one_ne_zero)
  simpa only [Real.one_rpow,Real.rpow_rpow_inv
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hp.ne'] using hh

lemma indices_top_of_values_top (f : ℕ → ℕ) {n : ℕ → ℕ}
    (h : Tendsto (fun i => (f (n i) : ℝ)) atTop atTop) : Tendsto n atTop atTop := by
  classical
  apply tendsto_atTop.2
  intro N
  let B := ∑ j ∈ range N, f j
  filter_upwards [h.eventually_ge_atTop ((B : ℝ)+1)] with i hi
  by_contra hn
  have hmem : n i ∈ range N := mem_range.mpr (by omega)
  have hle : f (n i) ≤ B := single_le_sum (fun j _ => Nat.zero_le (f j)) hmem
  have hleR : (f (n i) : ℝ) ≤ B := by exact_mod_cast hle
  linarith

/-- There is a sequence of support orders asymptotic to consecutive integers.
The chosen curvatures are exactly the power-law tangent curvatures. -/
theorem exists_centered_supports {f : ℕ → ℕ} {α c : ℝ} (ha : 0 < α)
    (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∃ (K : ℕ) (n : ℕ → ℕ), Tendsto n atTop atTop ∧
      (∀ i, QuadSupport f (c*α/2*((i+K+1 : ℕ) : ℝ)^(α-2)) (n i)) ∧
      Tendsto (fun i => (n i : ℝ)/((i+K+1 : ℕ) : ℝ)) atTop (𝓝 1) := by
  let C : ℝ := c*α/2
  let B : ℝ := (c-C)/2
  have hC : 0 < C := by dsimp [C]; positivity
  have hCc : C < c := by dsimp [C]; nlinarith
  have hB : 0 < B := by dsimp [B]; linarith
  have hBC : B+C < c := by dsimp [B]; linarith
  have hz : Tendsto (fun n : ℕ => (f n : ℝ)/(n : ℝ)^2) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using Erdos713FutureRecords.higher_ratio_zero ha2 h
  have hLow : ∀ᶠ k : ℕ in atTop, B*(k : ℝ)^α ≤
      (f k : ℝ)-(C*(k : ℝ)^(α-2))*(k : ℝ)^2 := by
    filter_upwards [(Erdos713FutureRecords.ratio_limit h).eventually_const_lt hBC,
      eventually_gt_atTop (0 : ℕ)] with k hk hkp
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkp
    have hh := (lt_div_iff₀ (Real.rpow_pos_of_pos hkR α)).mp hk
    rw [Real.rpow_sub hkR,Real.rpow_two]
    have he : C*((k : ℝ)^α/(k : ℝ)^2)*(k : ℝ)^2 = C*(k : ℝ)^α := by field_simp
    rw [he]
    nlinarith
  obtain ⟨K,hK⟩ := eventually_atTop.mp hLow
  let k : ℕ → ℕ := fun i => i+K+1
  have hkpos (i : ℕ) : 0 < k i := by dsimp [k]; omega
  have hkR (i : ℕ) : (0 : ℝ) < k i := by exact_mod_cast hkpos i
  have hki (i : ℕ) : K ≤ k i := by dsimp [k]; omega
  have hε (i : ℕ) : 0 < C*(k i : ℝ)^(α-2) :=
    mul_pos hC (Real.rpow_pos_of_pos (hkR i) _)
  have hPotential (i : ℕ) : 0 < (f (k i) : ℝ)-
      (C*(k i : ℝ)^(α-2))*(k i : ℝ)^2 :=
    (mul_pos hB (Real.rpow_pos_of_pos (hkR i) _)).trans_le (hK (k i) (hki i))
  choose n hn hMax using fun i => exists_support f hz (hε i) (hPotential i)
  have hk : Tendsto k atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with i hi
    dsimp [k]
    omega
  have hVal : Tendsto (fun i => (f (n i) : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (f := fun i => B*(k i : ℝ)^α) _
      (((tendsto_rpow_atTop ha).comp (tendsto_natCast_atTop_atTop.comp hk)).const_mul_atTop hB)
    intro i
    have hl := hK (k i) (hki i)
    have hh := hMax i
    have hnon : 0 ≤ (C*(k i : ℝ)^(α-2))*(n i : ℝ)^2 := by positivity
    linarith
  have hnt := indices_top_of_values_top f hVal
  exact ⟨K,n,hnt,hn,support_center_limit ha ha2 hc h hnt hk hn⟩

/-- Every sufficiently large order has a quadratic support in any fixed
relative window around it, with small curvature and large slope. -/
theorem nearby_supports {f : ℕ → ℕ} {α c : ℝ} (ha : 1 < α)
    (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (N D : ℕ) {δ η : ℝ} (hd : 0 < δ) (he : 0 < η) :
    ∀ᶠ k : ℕ in atTop, ∃ (n : ℕ) (ε : ℝ),
      N ≤ n ∧ 0 < n ∧ 0 < ε ∧ ε < η ∧ QuadSupport f ε n ∧
      (D : ℝ) ≤ ε*(2*(n : ℝ)-1) ∧
      (1-δ)*(k : ℝ) < n ∧ (n : ℝ) < (1+δ)*k := by
  have ha0 : 0 < α := by linarith
  obtain ⟨K,n,hn,hs,hr⟩ := exists_centered_supports ha0 ha2 hc h
  let k : ℕ → ℕ := fun i => i+K+1
  have hk : Tendsto k atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with i hi
    dsimp [k]
    omega
  have hC : 0 < c*α/2 := by positivity
  have hε : Tendsto (fun i => c*α/2*(k i : ℝ)^(α-2)) atTop (𝓝 0) := by
    have hh := ((tendsto_rpow_neg_atTop (show 0 < 2-α by linarith)).comp
      (tendsto_natCast_atTop_atTop.comp hk)).const_mul (c*α/2)
    simpa only [neg_sub,mul_zero] using hh
  have hDegree : Tendsto (fun i => c*(n i : ℝ)^(α-1)) atTop atTop :=
    ((tendsto_rpow_atTop (show 0 < α-1 by linarith)).comp
      (tendsto_natCast_atTop_atTop.comp hn)).const_mul_atTop hc
  have hConditions : ∀ᶠ i : ℕ in atTop,
      N ≤ n i ∧ 0 < n i ∧ c*α/2*(k i : ℝ)^(α-2) < η ∧
      (D : ℝ) ≤ (c*α/2*(k i : ℝ)^(α-2))*(2*(n i : ℝ)-1) ∧
      (1-δ)*(k i : ℝ) < n i ∧ (n i : ℝ) < (1+δ)*(k i : ℝ) := by
    filter_upwards [hn.eventually_ge_atTop N,hn.eventually_gt_atTop 0,
      hε.eventually_lt_const he,hDegree.eventually_ge_atTop (D : ℝ),
      hn.eventually (eventually_support_lower h (show c < c*α by nlinarith)),
      hr.eventually_const_lt (show 1-δ < 1 by linarith),
      hr.eventually_lt_const (show 1 < 1+δ by linarith)] with i hN hni heps hD hlo hrlo hrhi
    have hkpos : (0 : ℝ) < k i := by dsimp [k]; positivity
    exact ⟨hN,hni,heps,hD.trans (hlo _ (hs i)).le,
      (lt_div_iff₀ hkpos).mp hrlo,(div_lt_iff₀ hkpos).mp hrhi⟩
  obtain ⟨I,hI⟩ := eventually_atTop.mp hConditions
  filter_upwards [eventually_ge_atTop (I+K+1)] with j hj
  let i := j-(K+1)
  have hi : I ≤ i := by dsimp [i]; omega
  have hki : k i = j := by dsimp [i,k]; omega
  obtain ⟨hN,hni,heps,hD,hrlo,hrhi⟩ := hI i hi
  refine ⟨n i,c*α/2*(k i : ℝ)^(α-2),hN,hni,?_,heps,hs i,hD,?_,?_⟩
  · exact mul_pos hC (Real.rpow_pos_of_pos (by dsimp [k]; positivity) _)
  · simpa only [hki] using hrlo
  · simpa only [hki] using hrhi

#print axioms support_center_limit
#print axioms indices_top_of_values_top
#print axioms exists_centered_supports
#print axioms nearby_supports
end Erdos713QuadraticSupportCenters
