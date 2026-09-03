import Submission.GeneratingExplore

/-! Dominance of exponential/power scales and polynomial nonvanishing for
functions with an exponential times square-root asymptotic. -/
namespace Erdos66ExpPowerDominance
open Filter
open scoped Topology Classical
set_option maxHeartbeats 1800000

noncomputable def model (a b x : ℝ) : ℝ := Real.exp (a*x)*x^b

lemma model_pos (a b : ℝ) {x : ℝ} (hx : 0<x) : 0 < model a b x :=
  mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hx _)

lemma model_ratio (a b c d : ℝ) {x : ℝ} (hx : 0<x) :
    model a b x/model c d x=model (a-c) (b-d) x := by
  unfold model
  rw [sub_mul,Real.exp_sub,Real.rpow_sub hx]
  ring

lemma model_ratio_zero (a b c d : ℝ) (h : a<c ∨ a=c ∧ b<d) :
    Tendsto (fun x ↦ model a b x/model c d x) atTop (𝓝 0) := by
  rcases h with h | ⟨rfl,h⟩
  · have hh := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b-d) (c-a) (sub_pos.mpr h)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [model_ratio _ _ _ _ hx]
    dsimp only [model]
    rw [show -(c-a)*x=(a-c)*x by ring]
    ring
  · have hh := tendsto_rpow_neg_atTop (sub_pos.mpr h)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [model_ratio _ _ _ _ hx]
    simp only [model,sub_self,zero_mul,Real.exp_zero,one_mul]
    congr 1
    ring

lemma model_mul (a b c d : ℝ) {x : ℝ} (hx : 0<x) :
    model a b x*model c d x=model (a+c) (b+d) x := by
  unfold model
  rw [add_mul,Real.exp_add,Real.rpow_add hx]
  ring

lemma model_pow (a b : ℝ) (n : ℕ) {x : ℝ} (hx : 0<x) :
    model a b x^n=model (n*a) (n*b) x := by
  induction n with
  | zero => simp [model]
  | succ n ih =>
    rw [pow_succ,ih,model_mul _ _ _ _ hx]
    congr 1 <;> push_cast <;> ring

noncomputable def weight (p : ℕ×ℕ) : ℝ := (p.2 : ℝ)/2-p.1
noncomputable def monomial (F : ℝ → ℝ) (p : ℕ×ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x)^p.1*F x^p.2

lemma model_monomial (p : ℕ×ℕ) {x : ℝ} (hx : 0<x) :
    Real.exp (-x)^p.1*model (1/2) (1/2) x^p.2=model (weight p) (p.2/2) x := by
  have he : Real.exp (-x)=model (-1) 0 x := by simp [model]
  rw [he,model_pow _ _ _ hx,model_pow _ _ _ hx,model_mul _ _ _ _ hx]
  congr 1 <;> dsimp [weight] <;> ring

lemma monomial_normalization (F : ℝ → ℝ) (p : ℕ×ℕ) {x : ℝ} (hx : 0<x) :
    monomial F p x/model (weight p) (p.2/2) x=(F x/model (1/2) (1/2) x)^p.2 := by
  rw [←model_monomial p hx]
  unfold monomial
  rw [div_pow]
  have he := (Real.exp_pos (-x)).ne'
  have hm := (model_pos (1/2) (1/2) hx).ne'
  field_simp [he,hm]

lemma monomial_normalized_limit {F : ℝ → ℝ} {d : ℝ}
    (hF : Tendsto (fun x ↦ F x/model (1/2) (1/2) x) atTop (𝓝 d)) (p : ℕ×ℕ) :
    Tendsto (fun x ↦ monomial F p x/model (weight p) (p.2/2) x) atTop (𝓝 (d^p.2)) := by
  apply (hF.pow p.2).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (monomial_normalization F p hx).symm

lemma lower_monomial_limit {F : ℝ → ℝ} {d : ℝ}
    (hF : Tendsto (fun x ↦ F x/model (1/2) (1/2) x) atTop (𝓝 d))
    (p q : ℕ×ℕ) (h : weight p<weight q ∨ weight p=weight q ∧ p.2<q.2) :
    Tendsto (fun x ↦ monomial F p x/model (weight q) (q.2/2) x) atTop (𝓝 0) := by
  have hm := model_ratio_zero (weight p) (p.2/2) (weight q) (q.2/2) (by
    rcases h with h | ⟨he,hlt⟩
    · exact Or.inl h
    · exact Or.inr ⟨he,by
        have h' : (p.2 : ℝ)<q.2 := by exact_mod_cast hlt
        linarith⟩)
  have hh := (monomial_normalized_limit hF p).mul hm
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hp := (model_pos (weight p) (p.2/2) hx).ne'
  have hq := (model_pos (weight q) (q.2/2) hx).ne'
  field_simp [hp,hq]

lemma exists_dominant (S : Finset (ℕ×ℕ)) (hS : S.Nonempty) :
    ∃ q∈S, ∀ p∈S, p≠q → weight p<weight q ∨ weight p=weight q ∧ p.2<q.2 := by
  obtain ⟨q₀,hq₀,hmax⟩ := Finset.exists_max_image S weight hS
  let T := S.filter (fun p ↦ weight p=weight q₀)
  have hT : T.Nonempty := ⟨q₀,Finset.mem_filter.mpr ⟨hq₀,rfl⟩⟩
  obtain ⟨q,hq,hj⟩ := Finset.exists_max_image T Prod.snd hT
  obtain ⟨hqS,hqw⟩ := Finset.mem_filter.mp hq
  refine ⟨q,hqS,fun p hp hpq ↦ ?_⟩
  have hw : weight p ≤ weight q := (hmax p hp).trans_eq hqw.symm
  rcases lt_or_eq_of_le hw with h | h
  · exact Or.inl h
  · have hpT : p∈T := Finset.mem_filter.mpr ⟨hp,h.trans hqw⟩
    have hle : p.2≤q.2 := hj p hpT
    have hne : p.2≠q.2 := by
      intro he
      apply hpq
      apply Prod.ext _ he
      have hw' := h
      dsimp [weight] at hw'
      have he' : (p.2 : ℝ)=(q.2 : ℝ) := by exact_mod_cast he
      have hi : (p.1 : ℝ)=(q.1 : ℝ) := by linarith
      exact_mod_cast hi
    exact Or.inr ⟨h,lt_of_le_of_ne hle hne⟩

/-- A nonzero finite polynomial in exp(-x) and F(x) cannot vanish
arbitrarily far out when F(x)/(exp(x/2)sqrt(x)) has a nonzero limit. -/
theorem polynomial_eventually_ne_zero {F : ℝ → ℝ} {d : ℝ} (hd : d≠0)
    (hF : Tendsto (fun x ↦ F x/model (1/2) (1/2) x) atTop (𝓝 d))
    (S : Finset (ℕ×ℕ)) (hS : S.Nonempty) (a : ℕ×ℕ → ℝ) (ha : ∀ p∈S, a p≠0) :
    ∀ᶠ x in atTop, (∑ p∈S, a p*monomial F p x)≠0 := by
  obtain ⟨q,hq,hdom⟩ := exists_dominant S hS
  have ht (p : ℕ×ℕ) (hp : p∈S) :
      Tendsto (fun x ↦ a p*(monomial F p x/model (weight q) (q.2/2) x))
        atTop (𝓝 (if p=q then a q*d^q.2 else 0)) := by
    by_cases hpq : p=q
    · subst p
      simpa only [if_true] using (monomial_normalized_limit hF q).const_mul (a q)
    · simpa only [if_neg hpq,mul_zero] using (lower_monomial_limit hF p q (hdom p hp hpq)).const_mul (a p)
  have hh := tendsto_finset_sum S ht
  have hs : (∑ p∈S, if p=q then a q*d^q.2 else 0)=a q*d^q.2 := by simp [hq]
  rw [hs] at hh
  have hlim : Tendsto (fun x ↦ (∑ p∈S, a p*monomial F p x)/model (weight q) (q.2/2) x)
      atTop (𝓝 (a q*d^q.2)) := by
    apply hh.congr
    intro x
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  filter_upwards [hlim.eventually_ne (mul_ne_zero (ha q hq) (pow_ne_zero _ hd))] with x hx
  intro he
  exact hx (by rw [he,zero_div])

end Erdos66ExpPowerDominance
