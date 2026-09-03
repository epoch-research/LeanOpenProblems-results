import FormalConjecturesUtil

/-! Explicit odd-degree rounding for a growing finite-field mean. This is
scalar tuning of a field-plane size, not a natural-number set construction. -/
namespace Erdos66OddDegreeLogTuning
open Filter
open scoped Topology
set_option maxHeartbeats 1800000

lemma odd_degree_tuning (q : ℕ) (hq : 2≤q) (u c : ℝ) (hu : 0≤u) (hc : 0<c) :
    ∃ d : ℕ, Odd d ∧ 3≤d ∧
      0≤c-(u+q)^2/Real.log (((q^d)^2:ℕ):ℝ) ∧
      c-(u+q)^2/Real.log (((q^d)^2:ℕ):ℝ) ≤ 6*c^2*Real.log q/(q:ℝ)^2 := by
  let L := Real.log (q:ℝ)
  let μ := (u+q)^2
  have hq0 : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have hL : 0<L := Real.log_pos (by exact_mod_cast (show 1<q by omega))
  have hμ : 0<μ := by dsimp [μ]; positivity
  have hbase : (q:ℝ)^2≤μ := by dsimp [μ]; nlinarith
  let k := ⌈μ/(4*c*L)⌉₊
  have hx : 0<μ/(4*c*L) := by positivity
  have hklo : μ/(4*c*L)≤k := Nat.le_ceil _
  have hkhi : (k:ℝ)<μ/(4*c*L)+1 := Nat.ceil_lt_add_one hx.le
  have hk : 1≤k := by
    by_contra hh
    have he : k=0 := by omega
    rw [he,Nat.cast_zero] at hklo
    linarith
  let d := 2*k+1
  have hd : 3≤d := by dsimp [d]; omega
  have hlog : Real.log (((q^d)^2:ℕ):ℝ)=2*(d:ℝ)*L := by
    simp only [Nat.cast_pow,Real.log_pow]
    dsimp [L]
    ring
  have hden : 0<2*(d:ℝ)*L := by positivity
  have hlow : μ≤c*(2*(d:ℝ)*L) := by
    have hh := (div_le_iff₀ (by positivity : 0<4*c*L)).mp hklo
    dsimp only [d]
    push_cast
    nlinarith only [hh,mul_pos hc hL]
  have hup : c*(2*(d:ℝ)*L)-μ≤6*c*L := by
    have hh := (lt_div_iff₀' (by positivity : 0<4*c*L)).mp
      (show (k:ℝ)-1<μ/(4*c*L) by linarith)
    dsimp only [d]
    push_cast
    nlinarith only [hh]
  have hratio : 0≤c-μ/(2*(d:ℝ)*L) := by
    exact sub_nonneg.mpr ((div_le_iff₀ hden).mpr hlow)
  have herr : c-μ/(2*(d:ℝ)*L)≤6*c^2*L/μ := by
    have he : c-μ/(2*(d:ℝ)*L)=(c*(2*(d:ℝ)*L)-μ)/(2*(d:ℝ)*L) := by field_simp
    rw [he]
    have h₁ := div_le_div_of_nonneg_right hup hden.le
    have h₂ : 6*c*L/(2*(d:ℝ)*L)≤6*c^2*L/μ := by
      apply (div_le_div_iff₀ hden hμ).mpr
      have hh := mul_le_mul_of_nonneg_left hlow (show 0≤6*c*L by positivity)
      nlinarith only [hh]
    exact h₁.trans h₂
  have hbound : 6*c^2*L/μ≤6*c^2*L/(q:ℝ)^2 := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hbase
  refine ⟨d,⟨k,rfl⟩,hd,?_,?_⟩
  · simpa only [hlog] using hratio
  · simpa only [hlog] using herr.trans hbound

lemma tuning_cost_tendsto_zero (c : ℝ) :
    Tendsto (fun q : ℕ ↦ 6*c^2*Real.log q/(q:ℝ)^2) atTop (𝓝 0) := by
  have hlog : Tendsto (fun q : ℕ ↦ Real.log q/(q:ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun q : ℕ ↦ (q:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hh := (hlog.mul hinv).const_mul (6*c^2)
  simp only [mul_zero] at hh
  convert hh using 1
  funext q
  simp only [div_eq_mul_inv,pow_two,mul_inv_rev]
  ring

end Erdos66OddDegreeLogTuning
