import FormalConjecturesUtil

/-! A scalar obstruction to exponential peaks in a tower whose next factor
is itself bounded by a logarithmic representation budget. -/
namespace Erdos66ChangingFieldGrowth
open Filter
open scoped Topology
set_option maxHeartbeats 2200000

noncomputable def growthAllowance (C : ℝ) : ℝ :=
  16*C*Real.log (16*(C+1))+1

lemma growthAllowance_pos (C : ℝ) (hC : 0≤C) : 0<growthAllowance C := by
  have hl : 0≤Real.log (16*(C+1)) := Real.log_nonneg (by linarith)
  unfold growthAllowance
  positivity

/-- This uniform bound avoids an asymptotic hypothesis on the factors q.
The coefficient 5/4 is deliberately below sqrt(2). -/
lemma budget_one_step (x y q C : ℝ) (hx : 0≤x) (hq : 0<q) (hC : 0≤C)
    (hql : q≤y) (hrec : y=x+2*C*Real.log q) :
    y+growthAllowance C≤(5/4:ℝ)*(x+growthAllowance C) := by
  let d := 16*(C+1)
  have hd : 0<d := by dsimp [d]; linarith
  have hld : 0≤Real.log d := Real.log_nonneg (by dsimp [d]; linarith)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hq hd)
  rw [Real.log_div (ne_of_gt hq) (ne_of_gt hd)] at hlog
  have hscale : 2*C*q/d≤q/8 := by
    apply (div_le_iff₀ hd).mpr
    dsimp [d]
    nlinarith only [hq]
  rw [mul_div_assoc] at hscale
  have hm := mul_le_mul_of_nonneg_left (show Real.log q≤q/d+Real.log d by linarith)
    (show 0≤2*C by positivity)
  have hy : y≤x+y/8+2*C*Real.log d := by
    nlinarith only [hm,hscale,hql,hrec]
  have ha : 0≤2*C*Real.log d := by positivity
  change y+(16*C*Real.log d+1)≤(5/4:ℝ)*(x+(16*C*Real.log d+1))
  nlinarith only [hy,hx,ha]

/-- Under a logarithmic cap, field-size peaks force the cap budget to grow
by at most 5/4 per stage, after one fixed additive allowance. -/
lemma budget_bound (T q : ℕ → ℝ) (K C : ℝ) (hK : 0≤K) (hC : 0≤C)
    (hT : ∀ n, 0≤T n) (hq : ∀ n, 0<q n)
    (hrec : ∀ n, T (n+1)=T n+2*Real.log (q n))
    (hfield : ∀ n, q n≤K+C*T (n+1)) :
    ∀ n, K+C*T n+growthAllowance C≤
      (K+C*T 0+growthAllowance C)*(5/4:ℝ)^n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := budget_one_step (K+C*T n) (K+C*T (n+1)) (q n) C
      (add_nonneg hK (mul_nonneg hC (hT n))) (hq n) hC (hfield n) (by rw [hrec]; ring)
    have hm := mul_le_mul_of_nonneg_left ih (by norm_num : (0:ℝ)≤5/4)
    exact hs.trans (by simpa only [pow_succ] using (by
      convert hm using 1 <;> ring))

/-- No such budget can also dominate a factor-two peak every two stages. -/
theorem no_logarithmic_budget (T q : ℕ → ℝ) (K C : ℝ) (hK : 0≤K) (hC : 0≤C)
    (hT : ∀ n, 0≤T n) (hq : ∀ n, 0<q n)
    (hrec : ∀ n, T (n+1)=T n+2*Real.log (q n))
    (hfield : ∀ n, q n≤K+C*T (n+1))
    (hpeak : ∀ k, (2:ℝ)^k≤K+C*T (2*k)) : False := by
  have hb := budget_bound T q K C hK hC hT hq hrec hfield
  let S := K+C*T 0+growthAllowance C
  have hlim : Tendsto (fun k : ℕ ↦ S*(25/32:ℝ)^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤25/32)
        (by norm_num : (25/32:ℝ)<1)).const_mul S
  obtain ⟨k,hk⟩ := (hlim.eventually_lt_const (by norm_num : (0:ℝ)<1)).exists
  have he : S*(25/32:ℝ)^k=(S*(5/4:ℝ)^(2*k))/(2:ℝ)^k := by
    rw [pow_mul,mul_div_assoc,←div_pow]
    norm_num
  rw [he] at hk
  have hs := (div_lt_one (pow_pos (by norm_num : (0:ℝ)<2) k)).mp hk
  have ha := growthAllowance_pos C hC
  have hh := hb (2*k)
  change _≤S*(5/4:ℝ)^(2*k) at hh
  linarith only [hpeak k,hh,hs,ha]

end Erdos66ChangingFieldGrowth
