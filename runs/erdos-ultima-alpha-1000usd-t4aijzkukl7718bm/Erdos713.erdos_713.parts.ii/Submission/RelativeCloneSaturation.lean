import FormalConjecturesUtil
import Submission.QuadraticSupports

/-! Exactly extremal clone-saturated hosts with a uniform relative
minimum-degree lower bound. This is a necessary condition, not rationality. -/
open SimpleGraph Finset Filter Asymptotics
open scoped Topology
namespace Erdos713RelativeCloneSaturation
open Erdos713ExactCloneSaturation Erdos713QuadraticSupports Erdos713CloneSymm Erdos713Cloning
set_option maxHeartbeats 2000000

lemma eventually_doubling {f : ℕ → ℕ} {α c : ℝ} (ha : 1 < α) (hc : 0 < c)
    (h : (fun n : ℕ => (f n : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α)) :
    ∀ᶠ n : ℕ in atTop, 2*f n ≤ f (2*n) := by
  have htwo : Tendsto (fun n : ℕ => 2*n) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hpow : (2 : ℝ) < (2 : ℝ)^α := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) ha
  have hlim := Erdos713FutureRecords.ratio_limit h
  have hlim2 : Tendsto (fun n : ℕ => (f (2*n) : ℝ)/(n : ℝ)^α)
      atTop (𝓝 (c*(2 : ℝ)^α)) := by
    apply ((hlim.comp htwo).mul_const ((2 : ℝ)^α)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Function.comp_apply,Nat.cast_mul,Nat.cast_ofNat]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hnR.le]
    field_simp [(Real.rpow_pos_of_pos hnR α).ne',
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) α).ne']
  have hp : 0 < c*(2 : ℝ)^α-2*c := by nlinarith
  filter_upwards [((hlim2.sub (hlim.const_mul 2)).eventually_const_lt hp),
    eventually_gt_atTop (0 : ℕ)] with n hn hnp
  have hden : (0 : ℝ) < (n : ℝ)^α := Real.rpow_pos_of_pos (by exact_mod_cast hnp) α
  have hh : (2 : ℝ)*(f n : ℝ) < (f (2*n) : ℝ) := by
    have hh' : (2*(f n : ℝ))/(n : ℝ)^α < (f (2*n) : ℝ)/(n : ℝ)^α := by
      rw [mul_div_assoc]
      linarith
    exact (div_lt_div_iff_of_pos_right hden).mp hh'
  exact_mod_cast hh.le

lemma support_scale {f : ℕ → ℕ} {ε : ℝ} {n : ℕ}
    (hrec : QuadSupport f ε n) (hd : 2*f n ≤ f (2*n)) :
    (f n : ℝ) ≤ 3*ε*(n : ℝ)^2 := by
  have hh := hrec (2*n)
  have hdR : (2 : ℝ)*(f n : ℝ) ≤ f (2*n) := by exact_mod_cast hd
  push_cast at hh
  nlinarith only [hh,hdR]

lemma support_floor_scale {f : ℕ → ℕ} {ε : ℝ} {n : ℕ} (hn : 0 < n)
    (hε : 0 ≤ ε) (hrec : QuadSupport f ε n) (hd : 2*f n ≤ f (2*n))
    (hs : 1 ≤ ε*(2*(n : ℝ)-1)) :
    f n ≤ 6*n*⌊ε*(2*(n : ℝ)-1)⌋₊ := by
  let D := ⌊ε*(2*(n : ℝ)-1)⌋₊
  have hD : 1 ≤ D := Nat.le_floor (by simpa using hs)
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hfloor : ε*(2*(n : ℝ)-1) < (D : ℝ)+1 := Nat.lt_floor_add_one _
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : ε*(n : ℝ) ≤ ε*(2*(n : ℝ)-1) := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hbase (show (0 : ℝ) ≤ 3*n by positivity)
  have hprod' := mul_le_mul_of_nonneg_left hfloor.le (show (0 : ℝ) ≤ 3*n by positivity)
  have hh := support_scale hrec hd
  have hlast := mul_le_mul_of_nonneg_left (show (D : ℝ)+1 ≤ 2*D by linarith)
    (show (0 : ℝ) ≤ 3*n by positivity)
  have hbound : (f n : ℝ) ≤ 6*(n : ℝ)*D := by nlinarith only [hh,hprod,hprod',hlast]
  change f n ≤ 6*n*D
  exact_mod_cast hbound

lemma support_growth {f : ℕ → ℕ} (hf0 : f 0 = 0) {ε : ℝ} {n m : ℕ}
    (hε : 0 ≤ ε) (hrec : QuadSupport f ε n) (hm : m ≤ 2*n) :
    f m ≤ 4*f n := by
  have hzero := hrec 0
  simp only [hf0,Nat.cast_zero,zero_pow (by decide : 2 ≠ 0),zero_sub,mul_neg] at hzero
  have hmain := hrec m
  have hmR : (m : ℝ) ≤ 2*n := by exact_mod_cast hm
  have hsq : (m : ℝ)^2 ≤ 4*(n : ℝ)^2 := by nlinarith [sq_nonneg ((2 : ℝ)*n-m)]
  have hmε := mul_le_mul_of_nonneg_left hsq hε
  have hh : (f m : ℝ) ≤ 4*f n := by nlinarith only [hzero,hmain,hmε]
  exact_mod_cast hh

/-- Finite quantitative refinement. The output has a fold at every vertex,
exact extremal edge count, and minimum degree at least e/(24*order). -/
theorem exact_at_support_relative {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) {n D : ℕ} (hn : 0 < n)
    (hsize : (Fintype.card W+1)*(Fintype.card W)^2 ≤ n)
    (G : SimpleGraph (Fin n)) (hopt : OrdinaryOptimal H G)
    (he : Nat.card G.edgeSet = extremalNumber n H) {ε : ℝ} (hε : 0 < ε)
    (hrec : QuadSupport (fun m => extremalNumber m H) ε n)
    (hD : (max (max D (Fintype.card W)) 1 : ℝ) ≤ ε*(2*(n : ℝ)-1))
    (hsmall : ε*(((Fintype.card W+1)*(Fintype.card W)^2 : ℕ)^2 +
      ((Fintype.card W+1)*(Fintype.card W)^2 : ℕ) + (2 : ℝ)) < 1)
    (hdouble : 2*extremalNumber n H ≤ extremalNumber (2*n) H) :
    ∃ (U : Type) (_ : Fintype U) (J : SimpleGraph U),
      n ≤ Fintype.card U ∧ H.Free J ∧
      Nat.card J.edgeSet = extremalNumber (Fintype.card U) H ∧
      (∀ x, D ≤ Nat.card (J.neighborSet x)) ∧
      (∀ x, Nat.card J.edgeSet ≤ 24*Fintype.card U*Nat.card (J.neighborSet x)) ∧
      ∀ x, SingleFold H J x := by
  let d := ⌊ε*(2*(n : ℝ)-1)⌋₊
  have hd : max (max D (Fintype.card W)) 1 ≤ d := Nat.le_floor (by exact_mod_cast hD)
  have hQd : Fintype.card W ≤ d :=
    (le_max_right D (Fintype.card W)).trans ((le_max_left _ _).trans hd)
  have hDd : D ≤ d := (le_max_left D (Fintype.card W)).trans ((le_max_left _ _).trans hd)
  have hs : 1 ≤ ε*(2*(n : ℝ)-1) := (le_max_right _ _).trans hD
  have hdn : (d : ℝ) ≤ ε*(2*(n : ℝ)-1) := Nat.floor_le (by linarith)
  obtain ⟨U,instU,J,hnu,hun,hf,hE,hdeg,hfold⟩ :=
    exact_at_quadratic_support H hH hn hQd G hopt he hε hrec hdn hsmall
  have hscale : extremalNumber n H ≤ 6*n*d := support_floor_scale hn hε.le hrec hdouble hs
  have hGrowth : extremalNumber (Fintype.card U) H ≤ 4*extremalNumber n H :=
    support_growth (Erdos713Cloning.extremal_zero H) hε.le hrec (by omega)
  refine ⟨U,instU,J,hnu,hf,hE,fun x => hDd.trans (hdeg x),?_,hfold⟩
  intro x
  rw [hE]
  calc
    _ ≤ 4*(6*n*d) := hGrowth.trans (Nat.mul_le_mul_left _ hscale)
    _ = 24*n*d := by ring
    _ ≤ 24*Fintype.card U*Nat.card (J.neighborSet x) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hnu) (hdeg x)

/-- Cofinal exactly extremal hosts combining full clone saturation with a
uniform relative minimum degree. They need not be bipartite or secondary-optimal. -/
theorem exact_relative_saturated_cofinal {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hH : H.IsBipartite) (hEdge : ∃ a b, H.Adj a b) {α c : ℝ}
    (ha : 1 < α) (ha2 : α < 2) (hc : 0 < c)
    (h : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop]
      (fun n => c*(n : ℝ)^α)) (N D : ℕ) :
    ∃ (U : Type) (_ : Fintype U) (J : SimpleGraph U),
      N ≤ Fintype.card U ∧ H.Free J ∧
      Nat.card J.edgeSet = extremalNumber (Fintype.card U) H ∧
      (∀ x, D ≤ Nat.card (J.neighborSet x)) ∧
      (∀ x, Nat.card J.edgeSet ≤ 24*Fintype.card U*Nat.card (J.neighborSet x)) ∧
      ∀ x, SingleFold H J x := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (eventually_doubling ha hc h)
  let L : ℕ := (Fintype.card W+1)*(Fintype.card W)^2
  let A : ℝ := (L : ℝ)^2+L+2
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨n,ε,hnN,hn,hε,hsmall,hrec,hD⟩ := cofinal_supports
    (fun n => extremalNumber n H) (Erdos713Cloning.extremal_zero H) ha ha2 hc h
    (max (max N M) L) (max (max D (Fintype.card W)) 1)
    (show 0 < (1 : ℝ)/A by positivity)
  obtain ⟨G,hopt,he⟩ := exists_ordinary_optimal H hEdge n
  have hcurv : ε*(((Fintype.card W+1)*(Fintype.card W)^2 : ℕ)^2+
      ((Fintype.card W+1)*(Fintype.card W)^2 : ℕ)+(2 : ℝ)) < 1 := by
    have hh := (lt_div_iff₀ hA).mp hsmall
    simpa [A,L] using hh
  obtain ⟨U,instU,J,hnu,hf,hE,hdeg,hrelative,hfold⟩ :=
    exact_at_support_relative H hH hn ((le_max_right _ _).trans hnN) G hopt he hε hrec
      (by exact_mod_cast hD) hcurv
      (hM n (((le_max_right _ _).trans (le_max_left _ _)).trans hnN))
  exact ⟨U,instU,J,(((le_max_left _ _).trans (le_max_left _ _)).trans hnN).trans hnu,
    hf,hE,hdeg,hrelative,hfold⟩

#print axioms eventually_doubling
#print axioms support_floor_scale
#print axioms support_growth
#print axioms exact_at_support_relative
#print axioms exact_relative_saturated_cofinal
end Erdos713RelativeCloneSaturation
