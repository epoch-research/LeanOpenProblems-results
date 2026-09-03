import FormalConjecturesUtil
import Submission.PolynomialRateCriterion

/-! Constant-coefficient recurrences quantize pure-power exponents.
No recurrence for arbitrary graph extremal numbers is asserted. -/
open Filter Asymptotics Finset Polynomial Function
open scoped Topology fwdDiff
namespace Erdos713ConstantRecurrence
open Erdos713PolynomialRate
set_option maxHeartbeats 2000000

noncomputable def shift : Module.End ℝ (ℕ → ℝ) where
  toFun f n := f (n+1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def op (p : ℝ[X]) : Module.End ℝ (ℕ → ℝ) := Polynomial.aeval shift p

lemma shift_pow (k : ℕ) (f : ℕ → ℝ) (n : ℕ) : (shift^k) f n = f (n+k) := by
  induction k generalizing f n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,Module.End.mul_apply,ih]
    change f (n+k+1) = f (n+(k+1))
    congr 1

lemma op_apply (p : ℝ[X]) (f : ℕ → ℝ) (n : ℕ) :
    op p f n = ∑ i ∈ range (p.natDegree+1), p.coeff i*f (n+i) := by
  rw [op,Polynomial.aeval_eq_sum_range]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,shift_pow]

lemma op_mul (p q : ℝ[X]) (f : ℕ → ℝ) : op (p*q) f = op p (op q f) := by
  simp only [op,map_mul,Module.End.mul_apply]

lemma op_difference (f : ℕ → ℝ) : op (X-C 1) f = Δ_[1] f := by
  ext n
  simp [op,shift,fwdDiff]

lemma op_difference_pow (k : ℕ) (f : ℕ → ℝ) :
    op ((X-C 1)^k) f = (fwdDiff (1 : ℕ))^[k] f := by
  induction k generalizing f with
  | zero => simp [op]
  | succ k ih =>
    rw [pow_succ,op_mul,op_difference,ih,Function.iterate_succ_apply]

lemma higher_difference_zero {g : ℕ → ℝ} {k : ℕ} (hg : (fwdDiff (1 : ℕ))^[k] g = 0)
    (j : ℕ) (hj : k ≤ j) : (fwdDiff (1 : ℕ))^[j] g = 0 := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_comm k t,Function.iterate_add_apply,hg]
  clear hj
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply',ih]; ext n; simp [fwdDiff]

/-- Vanishing of a finite difference is used as an exact algebraic identity,
not as a consequence of asymptotic differentiation. -/
theorem polynomial_of_difference_zero {g : ℕ → ℝ} {k : ℕ}
    (hg : (fwdDiff (1 : ℕ))^[k] g = 0) : ∃ P : ℝ[X], ∀ n : ℕ, P.eval (n : ℝ) = g n := by
  classical
  let a (j : ℕ) : ℝ := ((fwdDiff (1 : ℕ))^[j] g) 0
  let P : ℝ[X] := ∑ j ∈ range k, C (a j/(j.factorial : ℝ))*descPochhammer ℝ j
  refine ⟨P,?_⟩
  intro n
  let F (j : ℕ) : ℝ := (n.choose j : ℝ)*a j
  have hzero (j : ℕ) (hj : k ≤ j) : F j = 0 := by
    simp only [F,a,higher_difference_zero hg j hj,Pi.zero_apply,mul_zero]
  have hleft : (∑ j ∈ range (n+1), F j) = ∑ j ∈ range (n+k+1), F j := by
    apply sum_subset (range_mono (by omega))
    intro j _ hj
    have hjn : n < j := by simpa only [mem_range,not_lt] using hj
    simp only [F,Nat.choose_eq_zero_of_lt hjn,Nat.cast_zero,zero_mul]
  have hright : (∑ j ∈ range k, F j) = ∑ j ∈ range (n+k+1), F j := by
    apply sum_subset (range_mono (by omega))
    intro j _ hj
    exact hzero j (by simpa only [mem_range,not_lt] using hj)
  have hnewton : g n = ∑ j ∈ range k, F j := by
    have h := shift_eq_sum_fwdDiff_iter (1 : ℕ) g n 0
    simp only [nsmul_eq_mul,Nat.cast_id,mul_one,zero_add] at h
    change g n = ∑ j ∈ range (n+1), F j at h
    exact h.trans (hleft.trans hright.symm)
  rw [hnewton]
  simp only [P,eval_finset_sum,eval_mul,eval_C]
  apply sum_congr rfl
  intro j _
  dsimp only [F]
  rw [Nat.cast_choose_eq_descPochhammer_div ℝ]
  ring

lemma shift_power_ratio (α : ℝ) (L : ℕ) :
    Tendsto (fun n : ℕ => ((n+L : ℕ) : ℝ)^α/(n : ℝ)^α) atTop (𝓝 1) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hs : Tendsto (fun n : ℕ => ((n+L : ℕ) : ℝ)/(n : ℝ)) atTop (𝓝 1) := by
    apply (show Tendsto (fun n : ℕ => 1+(L : ℝ)*(n : ℝ)⁻¹) atTop (𝓝 1) by
      simpa using (hi.const_mul (L : ℝ)).const_add 1).congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    push_cast
    field_simp
  have hh := hs.rpow_const (p := α) (Or.inl one_ne_zero)
  simpa only [Real.one_rpow,Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] using hh

lemma shifted_ratio_limit {f : ℕ → ℝ} {α c : ℝ}
    (hf : Tendsto (fun n : ℕ => f n/(n : ℝ)^α) atTop (𝓝 c)) (j : ℕ) :
    Tendsto (fun n : ℕ => f (n+j)/(n : ℝ)^α) atTop (𝓝 c) := by
  have ht : Tendsto (fun n : ℕ => n+j) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have h := (hf.comp ht).mul (shift_power_ratio α j)
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnj : (0 : ℝ) < (n+j : ℕ) := by exact_mod_cast (show 0 < n+j by omega)
  dsimp only [Function.comp_apply]
  field_simp [(Real.rpow_pos_of_pos hnj α).ne']

lemma op_ratio_limit {f : ℕ → ℝ} {α c : ℝ}
    (hf : Tendsto (fun n : ℕ => f n/(n : ℝ)^α) atTop (𝓝 c)) (p : ℝ[X]) :
    Tendsto (fun n : ℕ => op p f n/(n : ℝ)^α) atTop (𝓝 (p.eval 1*c)) := by
  have h := tendsto_finset_sum (range (p.natDegree+1))
    (fun j _ => (shifted_ratio_limit hf j).const_mul (p.coeff j))
  have he : (∑ j ∈ range (p.natDegree+1), p.coeff j*c) = p.eval 1*c := by
    rw [← sum_mul,eval_eq_sum_range]
    simp
  rw [he] at h
  simpa only [op_apply,sum_div,mul_div_assoc] using h

lemma ratio_to_larger_power_zero {f : ℕ → ℝ} {α β c : ℝ}
    (hf : Tendsto (fun n : ℕ => f n/(n : ℝ)^α) atTop (𝓝 c)) (hαβ : α < β) :
    Tendsto (fun n : ℕ => f n/(n : ℝ)^β) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ)^(α-β)) atTop (𝓝 0) := by
    simpa only [neg_sub] using (tendsto_rpow_neg_atTop (sub_pos.mpr hαβ)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  apply (show Tendsto (fun n : ℕ => (f n/(n : ℝ)^α)*(n : ℝ)^(α-β)) atTop (𝓝 0) by
    simpa using hf.mul hpow).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_sub hnR]
  field_simp [(Real.rpow_pos_of_pos hnR α).ne']

/-- A nonzero finite normalized polynomial limit determines the integer degree. -/
theorem exponent_eq_degree_of_polynomial_limit (P : ℝ[X]) {α c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n : ℕ => P.eval (n : ℝ)/(n : ℝ)^α) atTop (𝓝 c)) :
    α = (P.natDegree : ℝ) := by
  have hp : P ≠ 0 := by
    intro he
    subst P
    have hz : Tendsto (fun n : ℕ => (0 : ℝ)/(n : ℝ)^α) atTop (𝓝 0) := by simp
    exact hc (tendsto_nhds_unique h (by simpa only [Polynomial.eval_zero] using hz))
  have ha : (fun n : ℕ => P.eval (n : ℝ)) ~[atTop]
      (fun n : ℕ => P.leadingCoeff*(n : ℝ)^(P.natDegree : ℝ)) := by
    simpa only [Real.rpow_natCast] using P.isEquivalent_atTop_lead.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlead := ratio_limit ha
  rcases lt_trichotomy α (P.natDegree : ℝ) with hlt | he | hgt
  · exact (Polynomial.leadingCoeff_ne_zero.mpr hp
      (tendsto_nhds_unique hlead (ratio_to_larger_power_zero h hlt))).elim
  · exact he
  · exact (hc (tendsto_nhds_unique h (ratio_to_larger_power_zero hlead hgt))).elim

/-- Any nonzero constant-coefficient annihilating polynomial forces a
nonzero pure-power limit exponent to be a natural number. -/
theorem integer_exponent_of_annihilator {f : ℕ → ℝ} {α c : ℝ} (hc : c ≠ 0)
    (hf : Tendsto (fun n : ℕ => f n/(n : ℝ)^α) atTop (𝓝 c))
    (p : ℝ[X]) (hp : p ≠ 0) (hrec : op p f = 0) :
    ∃ d : ℕ, α = (d : ℝ) := by
  obtain ⟨q,hpq,hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp 1
  have hqeval : q.eval 1 ≠ 0 := by
    simpa only [Polynomial.dvd_iff_isRoot,Polynomial.IsRoot.def] using hq
  let g := op q f
  have hg : (fwdDiff (1 : ℕ))^[p.rootMultiplicity 1] g = 0 := by
    rw [← op_difference_pow,← op_mul,← hpq]
    exact hrec
  obtain ⟨P,hP⟩ := polynomial_of_difference_zero hg
  have hlim : Tendsto (fun n : ℕ => P.eval (n : ℝ)/(n : ℝ)^α)
      atTop (𝓝 (q.eval 1*c)) := by
    simpa only [hP,g] using op_ratio_limit hf q
  exact ⟨P.natDegree,exponent_eq_degree_of_polynomial_limit P (mul_ne_zero hqeval hc) hlim⟩

lemma op_shifted (p : ℝ[X]) (f : ℕ → ℝ) (L n : ℕ) :
    op p (fun m => f (m+L)) n = op p f (n+L) := by
  simp only [op_apply]
  apply sum_congr rfl
  intro j _
  congr 2
  omega

/-- Recurrences need only hold eventually. The normalization uses fixed-shift
ratio limits, not termwise asymptotics of differences. -/
theorem integer_exponent_of_eventual_annihilator
    {f : ℕ → ℝ} {α c : ℝ} (hc : c ≠ 0)
    (hf : Tendsto (fun n : ℕ => f n/(n : ℝ)^α) atTop (𝓝 c))
    (p : ℝ[X]) (hp : p ≠ 0) (hrec : ∀ᶠ n : ℕ in atTop, op p f n = 0) :
    ∃ d : ℕ, α = (d : ℝ) := by
  obtain ⟨L,hL⟩ := eventually_atTop.mp hrec
  apply integer_exponent_of_annihilator hc (shifted_ratio_limit hf L) p hp
  ext n
  rw [op_shifted]
  exact hL (n+L) (by omega)

theorem integer_exponent_of_equivalent
    {f : ℕ → ℝ} {α c : ℝ} (hc : c ≠ 0)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (p : ℝ[X]) (hp : p ≠ 0) (hrec : ∀ᶠ n : ℕ in atTop, op p f n = 0) :
    ∃ d : ℕ, α = (d : ℝ) :=
  integer_exponent_of_eventual_annihilator hc (ratio_limit hf) p hp hrec

/-- In the interval of the original conjecture, constant-coefficient
recurrence would force the exponent to be exactly one. -/
theorem exponent_eq_one_of_recurrence
    {f : ℕ → ℝ} {α c : ℝ} (hα : α ∈ Set.Ico 1 2) (hc : c ≠ 0)
    (hf : f ~[atTop] (fun n : ℕ => c*(n : ℝ)^α))
    (p : ℝ[X]) (hp : p ≠ 0) (hrec : ∀ᶠ n : ℕ in atTop, op p f n = 0) :
    α = 1 := by
  obtain ⟨d,rfl⟩ := integer_exponent_of_equivalent hc hf p hp hrec
  have hdlo : 1 ≤ d := by exact_mod_cast hα.1
  have hdhi : d < 2 := by exact_mod_cast hα.2
  have hd : d = 1 := by omega
  simp [hd]

#print axioms polynomial_of_difference_zero
#print axioms integer_exponent_of_annihilator
#print axioms integer_exponent_of_eventual_annihilator
#print axioms integer_exponent_of_equivalent
#print axioms exponent_eq_one_of_recurrence
end Erdos713ConstantRecurrence
