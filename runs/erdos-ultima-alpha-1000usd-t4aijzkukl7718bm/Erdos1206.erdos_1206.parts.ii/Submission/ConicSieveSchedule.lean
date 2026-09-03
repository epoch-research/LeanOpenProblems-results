import Submission.GeometricConicSource
import Submission.ConicSievePrimeEstimates

/-! Summable costs for the geometric conic sieve schedule. -/
namespace Erdos1206.ConicSieveSchedule
open Filter
open scoped Topology

noncomputable def m (L : ℝ) (j : ℕ) : ℕ := ⌈L*Real.exp ((3/2:ℝ)^j)⌉₊
noncomputable def r (L : ℝ) (j : ℕ) : ℕ := 16*m L j
noncomputable def z (L : ℝ) (j : ℕ) : ℕ := 2^m L j
noncomputable def cost (E : ℝ) (k : ℕ → ℕ) (j : ℕ) : ℝ :=
  Real.exp ((k j:ℝ)*Real.log 8)*
    (2*Real.exp (E-(7/4)*(3/2:ℝ)^j)+3*Real.exp (-10*(3/2:ℝ)^j))

lemma cost_nonneg (E : ℝ) (k : ℕ → ℕ) (j : ℕ) : 0 ≤ cost E k j := by
  dsimp only [cost]
  positivity

lemma m_pos {L : ℝ} (hL : 0 < L) (j : ℕ) : 0 < m L j :=
  Nat.ceil_pos.mpr (mul_pos hL (Real.exp_pos _))

lemma r_tendsto {L : ℝ} (hL : 0 < L) : Tendsto (r L) atTop atTop := by
  have ht : Tendsto (fun j : ℕ => L*Real.exp ((3/2:ℝ)^j)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt
      (by norm_num : (1:ℝ) < 3/2))).const_mul_atTop hL
  have hm : Tendsto (fun j : ℕ => (m L j:ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_ceil _) ht
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  simpa only [r,Nat.cast_mul,Nat.cast_ofNat] using
    hm.const_mul_atTop (by norm_num : (0:ℝ) < 16)

lemma r_succ_upper {L : ℝ} (hL : 0 < L) (j : ℕ) :
    (r L (j+1):ℝ) ≤ 16*(L+1)*Real.exp ((3/2:ℝ)*(3/2:ℝ)^j) := by
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ L*Real.exp ((3/2:ℝ)^(j+1)) by positivity)).le
  have he : (1:ℝ) ≤ Real.exp ((3/2:ℝ)^(j+1)) := Real.one_le_exp (by positivity)
  have hh : (m L (j+1):ℝ) ≤ (L+1)*Real.exp ((3/2:ℝ)^(j+1)) := by
    change (⌈L*Real.exp ((3/2:ℝ)^(j+1))⌉₊:ℝ) ≤ _
    nlinarith only [hc,he]
  simp only [r,Nat.cast_mul,Nat.cast_ofNat]
  rw [pow_succ,mul_comm ((3/2:ℝ)^j) (3/2)] at hh
  nlinarith only [hh]

lemma cost_upper (E : ℝ) (k : ℕ → ℕ) (j : ℕ) :
    cost E k j ≤ (2*Real.exp E+3)*
      Real.exp ((k j:ℝ)*Real.log 8-(7/4)*(3/2:ℝ)^j) := by
  have hp : 0 ≤ (3/2:ℝ)^j := by positivity
  have he : Real.exp (-10*(3/2:ℝ)^j) ≤ Real.exp (-(7/4)*(3/2:ℝ)^j) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ Real.exp ((k j:ℝ)*Real.log 8)*
        (2*Real.exp (E-(7/4)*(3/2:ℝ)^j)+3*Real.exp (-(7/4)*(3/2:ℝ)^j)) := by
      dsimp only [cost]
      gcongr
    _ = _ := by simp only [neg_mul,Real.exp_sub,Real.exp_neg]; ring

lemma band_cost_upper {L : ℝ} (hL : 0 < L) (E : ℝ) (k : ℕ → ℕ) (j : ℕ) :
    ((r L (j+1)-r L j:ℕ):ℝ)*cost E k j ≤
      (16*(L+1)*(2*Real.exp E+3))*Real.exp ((k j:ℝ)*Real.log 8-(1/4)*(3/2:ℝ)^j) := by
  have hr : ((r L (j+1)-r L j:ℕ):ℝ) ≤ (r L (j+1):ℝ) := by exact_mod_cast Nat.sub_le _ _
  have hR : 0 ≤ 16*(L+1)*Real.exp ((3/2:ℝ)*(3/2:ℝ)^j) := by positivity
  calc
    _ ≤ (16*(L+1)*Real.exp ((3/2:ℝ)*(3/2:ℝ)^j))*
        ((2*Real.exp E+3)*Real.exp ((k j:ℝ)*Real.log 8-(7/4)*(3/2:ℝ)^j)) :=
      mul_le_mul (hr.trans (r_succ_upper hL j)) (cost_upper E k j) (cost_nonneg E k j) hR
    _ = _ := by
      rw [show (16*(L+1)*Real.exp ((3/2:ℝ)*(3/2:ℝ)^j))*
          ((2*Real.exp E+3)*Real.exp ((k j:ℝ)*Real.log 8-(7/4)*(3/2:ℝ)^j)) =
          (16*(L+1)*(2*Real.exp E+3))*(Real.exp ((3/2:ℝ)*(3/2:ℝ)^j)*
            Real.exp ((k j:ℝ)*Real.log 8-(7/4)*(3/2:ℝ)^j)) by ring,←Real.exp_add]
      congr 2
      ring

lemma summable_geometric_exponential :
    Summable (fun j : ℕ => Real.exp (-(1/8)*(3/2:ℝ)^j)) := by
  have hh : Summable (fun j : ℕ => Real.exp ((j:ℝ)*(-1/16))) :=
    Real.summable_exp_nat_mul_iff.mpr (by norm_num)
  apply hh.of_nonneg_of_le (fun j => (Real.exp_pos _).le)
  intro j
  apply Real.exp_le_exp.mpr
  have hb := one_add_mul_sub_le_pow (by norm_num : (-1:ℝ) ≤ 3/2) j
  nlinarith only [hb]

/-- The source threshold is negligible on this scale, so the total cost over
all dyadic bands converges. -/
theorem summable_band_cost {L : ℝ} (hL : 0 < L) (E : ℝ) (k : ℕ → ℕ)
    (hk : Tendsto (fun j => (k j:ℝ)/(3/2:ℝ)^j) atTop (𝓝 0)) :
    Summable (fun j => ((r L (j+1)-r L j:ℕ):ℝ)*cost E k j) := by
  let C : ℝ := 16*(L+1)*(2*Real.exp E+3)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  apply (summable_geometric_exponential.mul_left C).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  have ht := hk.mul_const (Real.log 8)
  have hev : ∀ᶠ j : ℕ in atTop, ((k j:ℝ)/(3/2:ℝ)^j)*Real.log 8 < 1/8 := by
    exact ht.eventually (by simpa only [zero_mul] using
      (gt_mem_nhds (by norm_num : (0:ℝ) < 1/8)))
  filter_upwards [hev] with j hj
  have hp : 0 < (3/2:ℝ)^j := by positivity
  have hsmall : (k j:ℝ)*Real.log 8 ≤ (1/8)*(3/2:ℝ)^j := by
    have hh := (div_lt_iff₀ hp).mp (show ((k j:ℝ)*Real.log 8)/(3/2:ℝ)^j < 1/8 by
      simpa only [div_mul_eq_mul_div] using hj)
    linarith
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (cost_nonneg E k j))]
  exact (band_cost_upper hL E k j).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith)) hC)

#print axioms r_tendsto
#print axioms band_cost_upper
#print axioms summable_band_cost
end Erdos1206.ConicSieveSchedule
