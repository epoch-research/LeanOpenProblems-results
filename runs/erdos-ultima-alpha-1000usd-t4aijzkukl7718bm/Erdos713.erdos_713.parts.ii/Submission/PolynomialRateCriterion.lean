import FormalConjecturesUtil

/-! A finite Newton-polygon criterion for rationality of a pure-power exponent.
This is conditional: no polynomial relation for general graph extremal numbers
is assumed or established here. -/
open Filter Asymptotics
open scoped Topology
namespace Erdos713PolynomialRate

def weight (α : ℝ) (p : ℕ × ℕ) : ℝ := p.1 + α*p.2

lemma weight_injective {α : ℝ} (hα : α ∉ Set.range ((↑) : ℚ → ℝ)) :
    Function.Injective (weight α) := by
  intro p q h
  by_cases h₂ : p.2 = q.2
  · apply Prod.ext ?_ h₂
    have he : (p.1 : ℝ) = q.1 := by
      dsimp [weight] at h
      rw [h₂] at h
      linarith
    exact_mod_cast he
  · exfalso
    apply hα
    refine ⟨((q.1 : ℚ)-p.1)/((p.2 : ℚ)-q.2),?_⟩
    push_cast
    have hd : (p.2 : ℝ)-(q.2 : ℝ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h₂)
    apply (div_eq_iff hd).mpr
    dsimp [weight] at h
    nlinarith

lemma ratio_limit {f : ℕ → ℝ} {α c : ℝ}
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α)) :
    Tendsto (fun n : ℕ => f n/(n : ℝ)^α) atTop (𝓝 c) := by
  obtain ⟨φ,hφ,he⟩ := hf.exists_eq_mul
  have hh : Tendsto (fun n => φ n*c) atTop (𝓝 c) := by
    simpa using hφ.mul_const c
  apply hh.congr'
  filter_upwards [he,eventually_gt_atTop (0 : ℕ)] with n hn hpos
  change f n = φ n*(c*(n : ℝ)^α) at hn
  have hx : 0 < (n : ℝ) := by exact_mod_cast hpos
  rw [hn]
  field_simp [(Real.rpow_pos_of_pos hx α).ne']

lemma normalized_monomial (a y α β : ℝ) (p : ℕ × ℕ) {x : ℝ} (hx : 0 < x) :
    (a*x^p.1*y^p.2)/x^β =
      (a*(y/x^α)^p.2)*x^(weight α p-β) := by
  dsimp [weight]
  rw [Real.rpow_sub hx,Real.rpow_add hx,Real.rpow_natCast,
    Real.rpow_mul_natCast hx.le,div_pow]
  field_simp [(Real.rpow_pos_of_pos hx α).ne']

lemma term_limit {f : ℕ → ℝ} {α c β d : ℝ} (a : ℝ) (p : ℕ × ℕ)
    (hf : Tendsto (fun n : ℕ => f n/(n : ℝ)^α) atTop (𝓝 c))
    (hd : Tendsto (fun n : ℕ => (n : ℝ)^(weight α p-β)) atTop (𝓝 d)) :
    Tendsto (fun n : ℕ => (a*(n : ℝ)^p.1*(f n)^p.2)/(n : ℝ)^β)
      atTop (𝓝 (a*c^p.2*d)) := by
  apply ((tendsto_const_nhds.mul (hf.pow p.2)).mul hd).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (normalized_monomial a (f n) α β p (by exact_mod_cast hn)).symm

/-- A nonzero finite polynomial that vanishes arbitrarily far along a
pure-power sequence forces its exponent to be rational. -/
lemma rational_of_polynomial_relation {f : ℕ → ℝ} {α c : ℝ} (hc : c ≠ 0)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (s : Finset (ℕ × ℕ)) (hs : s.Nonempty) (a : (ℕ × ℕ) → ℝ)
    (ha : ∀ p ∈ s, a p ≠ 0)
    (hz : ∃ᶠ n : ℕ in atTop, ∑ p ∈ s, a p*(n : ℝ)^p.1*(f n)^p.2 = 0) :
    α ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  by_contra hα
  have hinj := weight_injective hα
  obtain ⟨r,hr,hmax⟩ := s.exists_max_image (weight α) hs
  have hlim := ratio_limit hf
  have hterms (p : ℕ × ℕ) (hp : p ∈ s) :
      Tendsto (fun n : ℕ => (a p*(n : ℝ)^p.1*(f n)^p.2)/(n : ℝ)^(weight α r))
        atTop (𝓝 (if p = r then a r*c^r.2 else 0)) := by
    by_cases he : p = r
    · subst p
      simp only [ite_true]
      have hh : Tendsto (fun n : ℕ => (n : ℝ)^(weight α r-weight α r))
          atTop (𝓝 (1 : ℝ)) := by simp
      simpa using term_limit (a r) r hlim hh
    · simp only [if_neg he]
      have hlt : weight α p < weight α r :=
        lt_of_le_of_ne (hmax p hp) (fun h => he (hinj h))
      have hh : Tendsto (fun n : ℕ => (n : ℝ)^(weight α p-weight α r))
          atTop (𝓝 (0 : ℝ)) := by
        simpa only [neg_sub] using
          (tendsto_rpow_neg_atTop (sub_pos.mpr hlt)).comp
            (tendsto_natCast_atTop_atTop (R := ℝ))
      simpa using term_limit (a p) p hlim hh
  have hsum := tendsto_finset_sum s hterms
  have hv : (∑ p ∈ s, if p = r then a r*c^r.2 else 0) = a r*c^r.2 := by simp [hr]
  rw [hv] at hsum
  have hnz := hsum.eventually_ne (mul_ne_zero (ha r hr) (pow_ne_zero _ hc))
  obtain ⟨n,hn,hn'⟩ := (hz.and_eventually hnz).exists
  apply hn'
  rw [← Finset.sum_div,hn,zero_div]

#print axioms rational_of_polynomial_relation
end Erdos713PolynomialRate
