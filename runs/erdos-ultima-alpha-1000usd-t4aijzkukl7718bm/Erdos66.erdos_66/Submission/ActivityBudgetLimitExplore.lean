import Submission.FiniteLogMassBudgetExplore

/-! A vanishing-error criterion for active-pair carry budgets.
It does not construct the coarse mass or an infinite Boolean set. -/
namespace Erdos66ActivityBudgetLimit
open Erdos66FiniteLogMassBudget Filter
open scoped Topology
set_option maxHeartbeats 1200000

lemma budget_div_identity (K P L : ℝ) (hK : 0 ≤ K) (hP : 0 ≤ P) (hL : 0<L) :
    budget K P/L=30*(K/L)+100*Real.sqrt ((K/L)*(P/L)) := by
  have hs : Real.sqrt ((K/L)*(P/L))=Real.sqrt (K*P)/L := by
    rw [div_mul_div_comm,←pow_two,Real.sqrt_div (mul_nonneg hK hP),Real.sqrt_sq hL.le]
  rw [hs,budget]
  ring

/-- No factor log of the orbit length is required: K=o(L) and P/L tending
to any finite value already make the full budget o(L). -/
theorem budget_div_limit (K P L : ℕ → ℝ) (c : ℝ)
    (hK : ∀ᶠ n in atTop, 0 ≤ K n) (hP : ∀ᶠ n in atTop, 0 ≤ P n)
    (hL : ∀ᶠ n in atTop, 0<L n)
    (hkl : Tendsto (fun n ↦ K n/L n) atTop (𝓝 0))
    (hpl : Tendsto (fun n ↦ P n/L n) atTop (𝓝 c)) :
    Tendsto (fun n ↦ budget (K n) (P n)/L n) atTop (𝓝 0) := by
  have hs := (hkl.mul hpl).sqrt
  have hh := (hkl.const_mul 30).add (hs.const_mul 100)
  simp only [zero_mul,mul_zero,Real.sqrt_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [hK,hP,hL] with n hk hp hl
  exact (budget_div_identity (K n) (P n) (L n) hk hp hl).symm

lemma constant_scale_ratio_limit (L : ℕ → ℝ) (c : ℝ)
    (hL : ∀ᶠ n in atTop, 0<L n) :
    Tendsto (fun n ↦ c*L n/L n) atTop (𝓝 c) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [hL] with n hn
  simp [hn.ne']

/-- A bounded normalized coarse mass is sufficient; it need not converge. -/
theorem budget_div_limit_of_bound (K P L : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hK : ∀ᶠ n in atTop, 0 ≤ K n) (hL : ∀ᶠ n in atTop, 0<L n)
    (hkl : Tendsto (fun n ↦ K n/L n) atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, P n ≤ C*L n) :
    Tendsto (fun n ↦ budget (K n) (P n)/L n) atTop (𝓝 0) := by
  have hcap : ∀ᶠ n in atTop, 0 ≤ C*L n := hL.mono (fun n hn ↦ mul_nonneg hC hn.le)
  have hh := budget_div_limit K (fun n ↦ C*L n) L C hK hcap hL hkl
    (constant_scale_ratio_limit L C hL)
  apply squeeze_zero' ?_ ?_ hh
  · filter_upwards [hK,hL] with n hk hl
    exact div_nonneg (budget_nonneg _ _ hk) hl.le
  · filter_upwards [hK,hL,hbound] with n hk hl hn
    exact div_le_div_of_nonneg_right (budget_mono_mass _ _ _ hk hn) hl.le

/-- A two-carry count inherits its proposed normalized mean when both
active-pair counts are subscale and both coarse masses have finite limits.
All the mean and support hypotheses remain explicit. -/
theorem two_budget_transfer (R μ K J P Q L : ℕ → ℝ) (c p q : ℝ)
    (hK : ∀ᶠ n in atTop, 0 ≤ K n) (hJ : ∀ᶠ n in atTop, 0 ≤ J n)
    (hP : ∀ᶠ n in atTop, 0 ≤ P n) (hQ : ∀ᶠ n in atTop, 0 ≤ Q n)
    (hL : ∀ᶠ n in atTop, 0<L n)
    (hkl : Tendsto (fun n ↦ K n/L n) atTop (𝓝 0))
    (hjl : Tendsto (fun n ↦ J n/L n) atTop (𝓝 0))
    (hpl : Tendsto (fun n ↦ P n/L n) atTop (𝓝 p))
    (hql : Tendsto (fun n ↦ Q n/L n) atTop (𝓝 q))
    (hμ : Tendsto (fun n ↦ μ n/L n) atTop (𝓝 c))
    (herr : ∀ᶠ n in atTop, |R n-μ n| ≤ budget (K n) (P n)+budget (J n) (Q n)) :
    Tendsto (fun n ↦ R n/L n) atTop (𝓝 c) := by
  have h1 := budget_div_limit K P L p hK hP hL hkl hpl
  have h2 := budget_div_limit J Q L q hJ hQ hL hjl hql
  have hsum := h1.add h2
  simp only [add_zero] at hsum
  have he : Tendsto (fun n ↦ (R n-μ n)/L n) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _)) ?_ hsum
    filter_upwards [herr,hL] with n hn hl
    rw [abs_div,abs_of_pos hl,←add_div]
    exact div_le_div_of_nonneg_right hn hl.le
  have hh := he.add hμ
  simp only [zero_add] at hh
  apply hh.congr
  intro n
  ring


/-- The two-carry transfer only needs upper bounds for the normalized coarse
masses, rather than limits for them. -/
theorem two_budget_transfer_of_bounds (R μ K J P Q L : ℕ → ℝ) (c C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hK : ∀ᶠ n in atTop, 0 ≤ K n) (hJ : ∀ᶠ n in atTop, 0 ≤ J n)
    (hL : ∀ᶠ n in atTop, 0<L n)
    (hkl : Tendsto (fun n ↦ K n/L n) atTop (𝓝 0))
    (hjl : Tendsto (fun n ↦ J n/L n) atTop (𝓝 0))
    (hP : ∀ᶠ n in atTop, P n ≤ C*L n)
    (hQ : ∀ᶠ n in atTop, Q n ≤ D*L n)
    (hμ : Tendsto (fun n ↦ μ n/L n) atTop (𝓝 c))
    (herr : ∀ᶠ n in atTop, |R n-μ n| ≤ budget (K n) (P n)+budget (J n) (Q n)) :
    Tendsto (fun n ↦ R n/L n) atTop (𝓝 c) := by
  apply two_budget_transfer R μ K J (fun n ↦ C*L n) (fun n ↦ D*L n) L c C D
    hK hJ (hL.mono (fun _ hn ↦ mul_nonneg hC hn.le))
    (hL.mono (fun _ hn ↦ mul_nonneg hD hn.le)) hL hkl hjl
    (constant_scale_ratio_limit L C hL) (constant_scale_ratio_limit L D hL) hμ
  filter_upwards [hK,hJ,hP,hQ,herr] with n hk hj hp hq he
  exact he.trans (add_le_add (budget_mono_mass _ _ _ hk hp) (budget_mono_mass _ _ _ hj hq))

end Erdos66ActivityBudgetLimit
