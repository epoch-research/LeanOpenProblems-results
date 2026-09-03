import FormalConjecturesUtil
import Submission.QuadraticSupportTangents
import Submission.RelativeExpansion

/-! Sharp minimum-degree coefficients on exactly extremal, fully
clone-obstructed hosts. This is a necessary condition, not rationality. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Topology
namespace Erdos713SharpSaturatedWitnesses
open Erdos713ExactCloneSaturation Erdos713QuadraticSupports
open Erdos713QuadraticSupportTangents Erdos713CloneSymm Erdos713Cloning
set_option maxHeartbeats 2000000

lemma shift_power_ratio (p : ℝ) (L : ℕ) :
    Tendsto (fun n : ℕ => ((n+L : ℕ) : ℝ)^p/(n : ℝ)^p) atTop (𝓝 1) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hs : Tendsto (fun n : ℕ => ((n+L : ℕ) : ℝ)/(n : ℝ)) atTop (𝓝 1) := by
    apply (show Tendsto (fun n : ℕ => 1+(L : ℝ)*(n : ℝ)⁻¹) atTop (𝓝 1) by
      simpa using (hi.const_mul (L : ℝ)).const_add 1).congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    push_cast
    field_simp
  have hh := hs.rpow_const (p := p) (Or.inl one_ne_zero)
  simpa only [Real.one_rpow,Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] using hh

lemma eventually_shift_gap {a b p : ℝ} (hab : a < b) (hp : 0 < p) (L : ℕ) :
    ∀ᶠ n : ℕ in atTop, a*((n+L : ℕ) : ℝ)^p+1 < b*(n : ℝ)^p := by
  have hz : Tendsto (fun n : ℕ => (n : ℝ)^(-p)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun n : ℕ =>
      a*(((n+L : ℕ) : ℝ)^p/(n : ℝ)^p)+(n : ℝ)^(-p)) atTop (𝓝 a) := by
    simpa using ((shift_power_ratio p L).const_mul a).add hz
  filter_upwards [hh.eventually_lt_const hab,eventually_gt_atTop (0 : ℕ)] with n hn hnp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnp
  have hpow := Real.rpow_pos_of_pos hnR p
  rw [Real.rpow_neg hnR.le,← one_div] at hn
  have he : a*(((n+L : ℕ) : ℝ)^p/(n : ℝ)^p)+1/(n : ℝ)^p =
      (a*((n+L : ℕ) : ℝ)^p+1)/(n : ℝ)^p := by ring
  rw [he] at hn
  exact (div_lt_iff₀ hpow).mp hn

/-- The minimum-degree coefficient can approach c*alpha on the SAME
exact extremal hosts on which every vertex has a single-fold obstruction. -/
theorem sharp_saturated_cofinal {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (hEdge : ∃ x y, H.Adj x y) {α c a : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c) (ha0 : 0 < a) (hac : a < c*α)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (N D : ℕ) :
    ∃ (U : Type) (_ : Fintype U) (J : SimpleGraph U),
      N ≤ Fintype.card U ∧ H.Free J ∧
      Nat.card J.edgeSet = extremalNumber (Fintype.card U) H ∧
      (∀ x, D ≤ Nat.card (J.neighborSet x)) ∧
      (∀ x, a*(Fintype.card U : ℝ)^(α-1) ≤ (Nat.card (J.neighborSet x) : ℝ)) ∧
      ∀ x, SingleFold H J x := by
  let L : ℕ := (Fintype.card W+1)*(Fintype.card W)^2
  let b : ℝ := (a+c*α)/2
  have hab : a < b := by dsimp [b]; linarith
  have hba : b < c*α := by dsimp [b]; linarith
  have hb : 0 < b := ha0.trans hab
  have hp : 0 < α-1 := by linarith
  have hlarge : ∀ᶠ n : ℕ in atTop,
      (max D (Fintype.card W) : ℝ)+1 ≤ b*(n : ℝ)^(α-1) :=
    (((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).const_mul_atTop hb).eventually_ge_atTop _
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    ((eventually_support_lower h hba).and ((eventually_shift_gap hab hp L).and hlarge))
  let A : ℝ := (L : ℝ)^2+L+2
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨n,ε,hnM,hn,hε,hεA,hrec,_⟩ := cofinal_supports
    (fun n => extremalNumber n H) (extremal_zero H) ha ha2 hc h
    (max N M) 0 (show 0 < (1 : ℝ)/A by positivity)
  obtain ⟨hlo,hgap,hNat⟩ := hM n ((le_max_right N M).trans hnM)
  let d : ℕ := ⌊b*(n : ℝ)^(α-1)⌋₊
  have hdle : (d : ℝ) ≤ b*(n : ℝ)^(α-1) := Nat.floor_le (by positivity)
  have hdgt : b*(n : ℝ)^(α-1) < (d : ℝ)+1 := Nat.lt_floor_add_one _
  have hdNat : max D (Fintype.card W) ≤ d := by
    exact_mod_cast (show (max D (Fintype.card W) : ℝ) ≤ d by linarith)
  have hdSlope : (d : ℝ) ≤ ε*(2*(n : ℝ)-1) := hdle.trans (hlo ε hrec).le
  obtain ⟨G,hopt,he⟩ := exists_ordinary_optimal H hEdge n
  have hcurv : ε*(((Fintype.card W+1)*(Fintype.card W)^2 : ℕ)^2+
      ((Fintype.card W+1)*(Fintype.card W)^2 : ℕ)+(2 : ℝ)) < 1 := by
    have hh := (lt_div_iff₀ hA).mp hεA
    simpa [A,L] using hh
  obtain ⟨U,hU,J,hnJ,hJupper,hfree,hE,hdeg,hfold⟩ :=
    exact_at_quadratic_support H hH hn ((le_max_right D _).trans hdNat)
      G hopt he hε hrec hdSlope hcurv
  refine ⟨U,hU,J,((le_max_left N M).trans hnM).trans hnJ,hfree,hE,
    fun x => ((le_max_left D _).trans hdNat).trans (hdeg x),?_,hfold⟩
  intro x
  have hcard : (Fintype.card U : ℝ) ≤ (n+L : ℕ) := by
    exact_mod_cast hJupper
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg (Fintype.card U)) hcard hp.le
  have hmul := mul_le_mul_of_nonneg_left hpow ha0.le
  have hd : (d : ℝ) ≤ (Nat.card (J.neighborSet x) : ℝ) := by exact_mod_cast hdeg x
  linarith

/-- One fixed expansion constant works while the sharp minimum-degree
coefficient approaches c*alpha. All conclusions concern the same host. -/
theorem sharp_saturated_expanding {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (hEdge : ∃ x y, H.Adj x y) {α c : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ a : ℝ, a < c*α → ∀ N D : ℕ,
      ∃ (U : Type) (_ : Fintype U) (J : SimpleGraph U),
        N ≤ Fintype.card U ∧ H.Free J ∧
        Nat.card J.edgeSet = extremalNumber (Fintype.card U) H ∧
        (∀ x, D ≤ Nat.card (J.neighborSet x)) ∧
        (∀ x, a*(Fintype.card U : ℝ)^(α-1) ≤ (Nat.card (J.neighborSet x) : ℝ)) ∧
        (∀ x, SingleFold H J x) ∧
        ∀ S : Finset U, 2*S.card ≤ Fintype.card U →
          κ*S.card*(Fintype.card U : ℝ)^(α-1) ≤
            (Nat.card (Erdos713SwitchGluing.cross J (S : Set U)).edgeSet : ℝ) := by
  obtain ⟨κ,hκ,hExp⟩ := Erdos713RelativeExpansion.eventually_expanding_exact H ha hc h
  have hUp : ∀ᶠ n : ℕ in atTop, (extremalNumber n H : ℝ) ≤ 2*c*(n : ℝ)^α := by
    filter_upwards [(Erdos713FutureRecords.ratio_limit h).eventually_lt_const
      (show c < 2*c by linarith),eventually_gt_atTop (0 : ℕ)] with n hn hnp
    exact ((div_lt_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hnp) α)).mp hn).le
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hExp.and hUp)
  refine ⟨κ,hκ,?_⟩
  intro a hac N D
  let b := max a c
  have hb0 : 0 < b := hc.trans_le (le_max_right _ _)
  have hbc : b < c*α := max_lt hac (by nlinarith)
  obtain ⟨U,hU,J,hN,hFree,hE,hD,hMin,hFold⟩ := sharp_saturated_cofinal
    H hH hEdge ha ha2 hc hb0 hbc h (max (max N M) 1) D
  have hNM : max N M ≤ Fintype.card U := (le_max_left _ _).trans hN
  have hMU : M ≤ Fintype.card U := (le_max_right _ _).trans hNM
  have hNU : N ≤ Fintype.card U := (le_max_left _ _).trans hNM
  have hpos : 0 < Fintype.card U := by have := (le_max_right (max N M) 1).trans hN; omega
  have hposR : (0 : ℝ) < Fintype.card U := by exact_mod_cast hpos
  have hfactor : (Fintype.card U : ℝ)^α =
      (Fintype.card U : ℝ)*(Fintype.card U : ℝ)^(α-1) := by
    rw [Real.rpow_sub hposR,Real.rpow_one]
    field_simp
  obtain ⟨hExpU,hUpU⟩ := hM (Fintype.card U) hMU
  have hRelative : ∀ v, Nat.card J.edgeSet ≤ 24*Fintype.card U*Nat.card (J.neighborSet v) := by
    intro v
    have hdegree : c*(Fintype.card U : ℝ)^(α-1) ≤
        (Nat.card (J.neighborSet v) : ℝ) :=
      (mul_le_mul_of_nonneg_right (le_max_right a c)
        (Real.rpow_nonneg hposR.le _)).trans (hMin v)
    rw [hfactor] at hUpU
    have hscale := mul_le_mul_of_nonneg_left hdegree (show 0 ≤ 2*(Fintype.card U : ℝ) by positivity)
    have hDeg0 : (0 : ℝ) ≤ Nat.card (J.neighborSet v) := Nat.cast_nonneg _
    have hbound : (extremalNumber (Fintype.card U) H : ℝ) ≤
        24*(Fintype.card U : ℝ)*(Nat.card (J.neighborSet v) : ℝ) := by nlinarith
    rw [hE]
    exact_mod_cast hbound
  refine ⟨U,hU,J,hNU,hFree,hE,hD,?_,hFold,?_⟩
  · intro x
    exact (mul_le_mul_of_nonneg_right (le_max_left a c)
      (Real.rpow_nonneg hposR.le _)).trans (hMin x)
  · exact hExpU U J rfl hFree hE hRelative

#print axioms shift_power_ratio
#print axioms eventually_shift_gap
#print axioms sharp_saturated_cofinal
#print axioms sharp_saturated_expanding
end Erdos713SharpSaturatedWitnesses
