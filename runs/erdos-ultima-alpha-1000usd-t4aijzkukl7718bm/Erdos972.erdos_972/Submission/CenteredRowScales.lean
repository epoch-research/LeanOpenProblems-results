import Submission.BeattyRowScales
import Submission.ChebyshevRowMean

/-! Common scales on which both unweighted and logarithmically weighted
fixed Beatty rows have sublinear error after common-endpoint centering. -/
namespace Erdos972CenteredRowScales

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972PrimePowerError Erdos972BeattyRows Erdos972BeattyRowScales
open Erdos972SelfCenteredLog Erdos972ChebyshevRowMean Erdos972ExponentialSum

lemma sublinear_nat_div {f : ℕ → ℝ} (hf : Tendsto (fun N : ℕ => f N/N) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) : Tendsto (fun N : ℕ => f (N/m)/N) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun N : ℕ => N/m) atTop atTop := le_of_eq (map_div_atTop_eq_nat m hm)
  have hh : Tendsto (fun N : ℕ => |f (N/m)/(N/m : ℕ)|) atTop (𝓝 0) := by
    simpa using (hf.comp hdiv).abs
  apply squeeze_zero_norm' _ hh
  filter_upwards [hdiv.eventually (eventually_ge_atTop (1 : ℕ)), eventually_ge_atTop (1 : ℕ)] with N hL hN
  have hL0 : (0 : ℝ) < (N/m : ℕ) := Nat.cast_pos.mpr hL
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  simp only [Real.norm_eq_abs, abs_div, abs_of_nonneg hL0.le, abs_of_nonneg hN0.le]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hL0 (Nat.cast_le.mpr (Nat.div_le_self N m))

noncomputable def endpointBudget (α : ℝ) (N : ℕ) : ℝ :=
  (1+Real.log N)*(2*Real.log (α*N)+7)

lemma endpointBudget_div_tendsto {α : ℝ} (hα : 0 < α) :
    Tendsto (fun N : ℕ => endpointBudget α N/N) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N/N) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop)
  have hlog2 : Tendsto (fun N : ℕ => Real.log N^2/N) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, Real.rpow_one, Function.comp_def] using
      ((isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop)
  have hh : Tendsto (fun N : ℕ => 2*(Real.log N^2/N)+(2*Real.log α+9)*(Real.log N/N)+(2*Real.log α+7)/N)
      atTop (𝓝 0) := by
    simpa using ((hlog2.const_mul 2).add (hlog.const_mul (2*Real.log α+9))).add
      (tendsto_const_div_atTop_nhds_zero_nat (2*Real.log α+7))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  unfold endpointBudget
  rw [Real.log_mul hα.ne' hN0]
  ring

lemma eventually_row_center_errors {α : ℝ} (hα : 1 < α) (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, endpointBudget α N ≤ ε*N ∧
      ∀ m ∈ Ioc 0 M, |selfCenteredLog (rowMean (α*m)) (N/m)| ≤ ε*N := by
  have hα0 : 0 < α := by linarith
  have he := (tendsto_order.mp (endpointBudget_div_tendsto hα0)).2 ε hε
  have hs : ∀ᶠ N : ℕ in atTop, ∀ m ∈ Ioc 0 M,
      |selfCenteredLog (rowMean (α*m)) (N/m)/N| < ε := by
    apply (eventually_all_finset (Ioc 0 M)).mpr
    intro m hm
    have hm0 := (mem_Ioc.mp hm).1
    have hh := sublinear_nat_div (selfCenteredRowMean_tendsto (show 0 < α*m by positivity)) hm0
    have hh' : Tendsto (fun N : ℕ => |selfCenteredLog (rowMean (α*m)) (N/m)/N|) atTop (𝓝 0) := by
      simpa using hh.abs
    exact (tendsto_order.mp hh').2 ε hε
  filter_upwards [he, hs, eventually_ge_atTop (1 : ℕ)] with N he hs hN
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  refine ⟨((div_lt_iff₀ hN0).mp he).le, ?_⟩
  intro m hm
  have hh := hs m hm
  rw [abs_div, abs_of_nonneg hN0.le] at hh
  exact ((div_lt_iff₀ hN0).mp hh).le

noncomputable def scaleCutoff (α : ℝ) (u : ℕ) : ℕ := ⌊(u : ℝ)^6/α⌋₊

lemma scaleCutoff_bounds {α : ℝ} (hα : 1 ≤ α) {u : ℕ} (hu : 0 < u) (hαu : α ≤ u) :
    u ≤ scaleCutoff α u ∧ scaleCutoff α u ≤ u^6 ∧ (u : ℝ)^6 ≤ 2*α*scaleCutoff α u := by
  have hα0 : 0 < α := by linarith
  have huR : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hpow : (u : ℝ)^2 ≤ (u : ℝ)^6 := by exact_mod_cast Nat.pow_le_pow_right hu (by norm_num : 2 ≤ 6)
  have hlow : u ≤ scaleCutoff α u := by
    apply Nat.le_floor
    apply (le_div_iff₀ hα0).mpr
    nlinarith
  refine ⟨hlow, ?_, ?_⟩
  · have hh := Nat.floor_mono (show (u : ℝ)^6/α ≤ (u : ℝ)^6 by
      apply (div_le_iff₀ hα0).mpr
      nlinarith [pow_nonneg huR.le 6])
    simpa only [scaleCutoff, ← Nat.cast_pow, Nat.floor_natCast] using hh
  · have hh := Nat.lt_floor_add_one ((u : ℝ)^6/α)
    have hN1 : (1 : ℝ) ≤ scaleCutoff α u := by exact_mod_cast hu.trans_le hlow
    have he := (div_lt_iff₀ hα0).mp hh
    change (u : ℝ)^6 < ((scaleCutoff α u : ℝ)+1)*α at he
    nlinarith

lemma scaleCutoff_row_eligible {α : ℝ} (hα : 1 ≤ α) (u m L : ℕ) (hL : L ≤ scaleCutoff α u/m) :
    floorMul (α*m) L ≤ u^6 := by
  have hα0 : 0 < α := by linarith
  have hmul : L*m ≤ scaleCutoff α u := (Nat.mul_le_mul_right m hL).trans (Nat.div_mul_le_self _ _)
  have hcut : (scaleCutoff α u : ℝ) ≤ (u : ℝ)^6/α := Nat.floor_le (by positivity)
  have htarget : (α*m)*L ≤ (u : ℝ)^6 := by
    have hh : (L : ℝ)*m ≤ scaleCutoff α u := by exact_mod_cast hmul
    have hh' := (le_div_iff₀ hα0).mp hcut
    nlinarith
  have hh := Nat.floor_mono htarget
  simpa only [floorMul, ← Nat.cast_pow, Nat.floor_natCast] using hh

/-- All finitely many fixed Type-I rows have small centered error at a common,
arbitrarily large cutoff. Both the unweighted and logarithmically weighted
rows are controlled. This theorem does not estimate the Type-II term. -/
theorem exists_common_centered_row_scale {α : ℝ} (hα : 1 < α) (hI : Irrational α)
    (M : ℕ) {ε : ℝ} (hε : 0 < ε) (B : ℕ) :
    ∃ N : ℕ, B < N ∧ ∀ m ∈ Ioc 0 M,
      |(∑ n ∈ Ioc 0 (N/m), (vonMangoldt (floorMul (α*m) n)-commonMean α N))| ≤ ε*N ∧
      |centeredLogRow (fun n => vonMangoldt (floorMul (α*m) n)) (commonMean α N) (N/m)| ≤ ε*N := by
  have hα0 : 0 < α := by linarith
  let η := ε/(48*α)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_row_center_errors hα M (show 0 < ε/4 by positivity))
  let C := max B (max T (⌈α⌉₊+1))
  obtain ⟨u, huC, hrows⟩ := exists_common_beatty_row_scale hα hI M 1 hη C
  have hu : 0 < u := lt_of_le_of_lt (Nat.zero_le C) huC
  have hαu : α ≤ u := by
    have hh : ⌈α⌉₊+1 ≤ C := (le_max_right T _).trans (le_max_right B _)
    exact (Nat.le_ceil α).trans (by exact_mod_cast (Nat.le_trans (Nat.le_succ _) (hh.trans huC.le)))
  let N := scaleCutoff α u
  obtain ⟨huN, hNpow, hscale⟩ := scaleCutoff_bounds hα.le hu hαu
  have hN : 0 < N := hu.trans_le huN
  have hNu : (N : ℝ) ≤ (u : ℝ)^6 := by exact_mod_cast hNpow
  have hscale' : (u : ℝ)^6 ≤ 2*α*N := hscale
  have hTN : T ≤ N := (le_max_left T _).trans ((le_max_right B _).trans (huC.le.trans huN))
  obtain ⟨hend, hself⟩ := hT N hTN
  have hBN : B < N := (le_max_left _ _).trans_lt (huC.trans_le huN)
  have hS : 1 ≤ 1+Real.log u := by linarith [Real.log_natCast_nonneg u]
  have hS0 : 0 < 1+Real.log u := by linarith
  let E := η*(u : ℝ)^6/(1+Real.log u)
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hEscale : E ≤ η*(u : ℝ)^6 := by
    dsimp [E]
    exact div_le_self (by positivity) hS
  have hcost : 12*η*(u : ℝ)^6 ≤ (ε/2)*N := by
    have hh := mul_le_mul_of_nonneg_left hscale' (show 0 ≤ 12*η by positivity)
    have he : 12*η*(2*α*N) = (ε/2)*N := by dsimp [η]; field_simp; ring
    exact hh.trans_eq he
  refine ⟨N, hBN, ?_⟩
  intro m hm
  obtain ⟨hm0, hmM⟩ := mem_Ioc.mp hm
  let L := N/m
  let a := fun n => (vonMangoldt (floorMul (α*m) n) : ℝ)
  let F := rowMean (α*m)
  have hL : L ≤ N := Nat.div_le_self N m
  have hlogL0 : 0 ≤ Real.log L := Real.log_natCast_nonneg L
  have hlogN0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hlogL : Real.log L ≤ Real.log N := monotone_log_natCast hL
  have hlogu : Real.log N ≤ 6*Real.log u := by
    have hh := monotone_log_natCast hNpow
    dsimp only at hh
    rw [Nat.cast_pow, Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have hprefix : ∀ j ≤ L, |(∑ n ∈ Ioc 0 j, a n)-F j| ≤ E := by
    intro j hj
    have hh := hrows m hm0 hmM j (scaleCutoff_row_eligible hα.le u m j hj)
    simp only [pow_one] at hh
    exact (le_div_iff₀ hS0).mpr hh
  have hweightedCost : 2*Real.log L*E ≤ (ε/2)*N := by
    have hl : Real.log L ≤ 6*(1+Real.log u) := by linarith
    calc
      _ ≤ 2*(6*(1+Real.log u))*E := by gcongr
      _ = 12*η*(u : ℝ)^6 := by dsimp [E]; field_simp; norm_num
      _ ≤ _ := hcost
  have hunweightedCost : E ≤ (ε/2)*N := by
    have hh : η*(u : ℝ)^6 ≤ 12*η*(u : ℝ)^6 := by
      nlinarith [mul_nonneg hη.le (pow_nonneg (Nat.cast_nonneg (α := ℝ) u) 6)]
    exact hEscale.trans (hh.trans hcost)
  have hepoint := common_row_endpoint_bound hα.le hm0 hN
  have hR : 0 ≤ 2*Real.log (α*N)+7 := by
    have hh : 1 ≤ α*N := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    have hh' := Real.log_nonneg hh
    linarith
  have hepoint' : |F L-commonMean α N*L| ≤ endpointBudget α N := by
    apply hepoint.trans
    unfold endpointBudget
    nlinarith
  have heweighted : Real.log L*|F L-commonMean α N*L| ≤ endpointBudget α N := by
    calc
      _ ≤ Real.log N*(2*Real.log (α*N)+7) := by gcongr
      _ ≤ _ := by unfold endpointBudget; nlinarith
  constructor
  · have heq : (∑ n ∈ Ioc 0 L, (a n-commonMean α N)) = (∑ n ∈ Ioc 0 L, a n)-commonMean α N*L := by
      simp only [sum_sub_distrib, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
      ring
    change |∑ n ∈ Ioc 0 L, (a n-commonMean α N)| ≤ ε*N
    rw [heq]
    have hh := (abs_sub_le (∑ n ∈ Ioc 0 L, a n) (F L) (commonMean α N*L)).trans
      (add_le_add (hprefix L le_rfl) hepoint')
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  · have hh := centeredLogRow_bound a F (rowMean_zero (α*m)) (commonMean α N) L E hprefix
    have hs := hself m hm
    change |selfCenteredLog F L| ≤ (ε/4)*N at hs
    change |centeredLogRow a (commonMean α N) L| ≤ ε*N
    linarith

#print axioms exists_common_centered_row_scale

#print axioms eventually_row_center_errors
#print axioms scaleCutoff_bounds

end Erdos972CenteredRowScales
