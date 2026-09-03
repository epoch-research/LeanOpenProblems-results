import Submission.CommonLogCenter
import Submission.SlowOscillationTauberian

/-! Elementary bounds and slow oscillation of the reciprocal Möbius sums. -/
namespace Erdos972MobiusPartialSums

open Finset Filter MeasureTheory Set ArithmeticFunction
open scoped ArithmeticFunction.Moebius Topology
open Erdos972CommonLogCenter

noncomputable def reciprocalMoebius (N : ℕ) : ℝ := ∑ n ∈ Finset.Ioc 0 N, (μ n : ℝ)/n
noncomputable def reciprocalMoebiusReal (x : ℝ) : ℝ := reciprocalMoebius ⌊x⌋₊
noncomputable def logMoebius (t : ℝ) : ℝ := if 0 < t then reciprocalMoebiusReal (Real.exp t) else 0

lemma reciprocalMoebius_bound (N : ℕ) : |reciprocalMoebius N| ≤ 2 := reciprocal_moebius_sum_bound N

lemma logMoebius_bound (t : ℝ) : ‖logMoebius t‖ ≤ 2 := by
  rw [Real.norm_eq_abs]
  unfold logMoebius
  split_ifs
  · exact reciprocalMoebius_bound _
  · norm_num

lemma measurable_reciprocalMoebiusReal : Measurable reciprocalMoebiusReal :=
  (measurable_of_countable reciprocalMoebius).comp Nat.measurable_floor

lemma measurable_logMoebius : Measurable logMoebius :=
  (measurable_reciprocalMoebiusReal.comp Real.continuous_exp.measurable).ite measurableSet_Ioi measurable_const

lemma reciprocalMoebius_interval {A B : ℕ} (hAB : A ≤ B) :
    |reciprocalMoebius B-reciprocalMoebius A| ≤ ((B-A : ℕ) : ℝ)/((A : ℝ)+1) := by
  have he : reciprocalMoebius B-reciprocalMoebius A =
      ∑ n ∈ Finset.Ioc A B, (μ n : ℝ)/n := by
    have hh := Finset.sum_Ioc_consecutive (fun n => (μ n : ℝ)/n) (Nat.zero_le A) hAB
    dsimp only [reciprocalMoebius]
    linarith only [hh]
  rw [he]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Finset.Ioc A B, 1/((A : ℝ)+1) := by
      apply sum_le_sum
      intro n hn
      have hAn : (A : ℝ)+1 ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
      have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := n)
      rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
      exact (div_le_div_of_nonneg_right hμ (Nat.cast_nonneg _)).trans
        (one_div_le_one_div_of_le (by positivity) hAn)
    _ = _ := by simp [div_eq_mul_inv]

lemma reciprocalMoebiusReal_interval {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    |reciprocalMoebiusReal y-reciprocalMoebiusReal x| ≤ (y-x+1)/x := by
  have hf : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
  have hcard : ((⌊y⌋₊-⌊x⌋₊ : ℕ) : ℝ) ≤ y-x+1 := by
    rw [Nat.cast_sub hf]
    linarith only [Nat.floor_le (hx.le.trans hxy), Nat.lt_floor_add_one x]
  apply (reciprocalMoebius_interval hf).trans
  exact (div_le_div_of_nonneg_right hcard (by positivity)).trans
    (div_le_div_of_nonneg_left (by linarith only [hxy] : 0 ≤ y-x+1) hx (Nat.lt_floor_add_one x).le)

lemma reciprocalMoebiusReal_local {a b x y : ℝ} (ha : 0 < a)
    (hax : a ≤ x) (hxb : x ≤ b) (hay : a ≤ y) (hyb : y ≤ b) :
    |reciprocalMoebiusReal x-reciprocalMoebiusReal y| ≤ (b-a+1)/a := by
  have hb0 : 0 ≤ b-a+1 := by linarith only [hax, hxb]
  rcases le_total x y with hxy | hyx
  · rw [abs_sub_comm]
    apply (reciprocalMoebiusReal_interval (ha.trans_le hax) hxy).trans
    exact (div_le_div_of_nonneg_right (by linarith only [hax, hyb]) (ha.le.trans hax)).trans
      (div_le_div_of_nonneg_left hb0 ha hax)
  · apply (reciprocalMoebiusReal_interval (ha.trans_le hay) hyx).trans
    exact (div_le_div_of_nonneg_right (by linarith only [hay, hxb]) (ha.le.trans hay)).trans
      (div_le_div_of_nonneg_left hb0 ha hay)

lemma logMoebius_local {δ x u : ℝ} (hδ : 0 < δ) (hx : δ < x) (hu : u ∈ Set.Ioo (-δ) δ) :
    |logMoebius (x+u)-logMoebius x| ≤ Real.exp (2*δ)-1+Real.exp (δ-x) := by
  have hx0 : 0 < x := hδ.trans hx
  have hxu : 0 < x+u := by linarith only [hx, hu.1]
  simp only [logMoebius, if_pos hx0, if_pos hxu]
  have hh := reciprocalMoebiusReal_local (Real.exp_pos (x-δ))
    (Real.exp_le_exp.mpr (show x-δ ≤ x+u by linarith only [hu.1]))
    (Real.exp_le_exp.mpr (show x+u ≤ x+δ by linarith only [hu.2]))
    (Real.exp_le_exp.mpr (show x-δ ≤ x by linarith only [hδ]))
    (Real.exp_le_exp.mpr (show x ≤ x+δ by linarith only [hδ]))
  have he : (Real.exp (x+δ)-Real.exp (x-δ)+1)/Real.exp (x-δ) =
      Real.exp (2*δ)-1+Real.exp (δ-x) := by
    have h₁ : Real.exp (x+δ) = Real.exp (x-δ)*Real.exp (2*δ) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h₂ : Real.exp (δ-x) = 1/Real.exp (x-δ) := by
      rw [show δ-x = -(x-δ) by ring, Real.exp_neg, one_div]
    rw [h₁, h₂]
    field_simp
  exact hh.trans_eq he

/-- The reciprocal Möbius sum is slowly oscillating on the logarithmic scale,
using only the pointwise bound `|μ(n)| ≤ 1`. -/
theorem logMoebius_slow : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ᶠ x : ℝ in atTop, ∀ u ∈ Set.Ioo (-δ) δ, |logMoebius (x+u)-logMoebius x| ≤ ε := by
  intro ε hε
  let δ := Real.log (1+ε/2)/2
  have hδ : 0 < δ := div_pos (Real.log_pos (by linarith)) (by norm_num)
  have hE : Real.exp (2*δ)-1 = ε/2 := by
    have he : 2*δ = Real.log (1+ε/2) := by dsimp [δ]; ring
    rw [he, Real.exp_log (by linarith : 0 < 1+ε/2)]
    ring
  have hlim : Tendsto (fun x : ℝ => Real.exp (δ-x)) atTop (𝓝 0) := by
    have hh : Tendsto (fun x : ℝ => 1/Real.exp (x-δ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_exp_atTop.comp (by
        simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-δ) tendsto_id))
    convert hh using 1
    funext x
    rw [show δ-x = -(x-δ) by ring, Real.exp_neg, one_div]
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [eventually_gt_atTop δ, (tendsto_order.mp hlim).2 (ε/2) (by positivity)] with x hx hxε
  intro u hu
  have hh := logMoebius_local hδ hx hu
  rw [hE] at hh
  linarith only [hh, hxε]

#print axioms logMoebius_slow

end Erdos972MobiusPartialSums
