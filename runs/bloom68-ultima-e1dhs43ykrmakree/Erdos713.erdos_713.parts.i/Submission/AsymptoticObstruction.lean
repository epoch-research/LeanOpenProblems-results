import FormalConjecturesUtil

/-!
# A sufficient analytic obstruction to a pure-power extremal asymptotic

This development lemma does not assert that any graph has the hypotheses below.
It verifies the analytic step that would turn a little-o upper bound together
with matching exponent lower bounds into a counterexample.
-/

open Filter Asymptotics
open scoped Topology

namespace Erdos713

private lemma nat_rpow_isLittleO {a b : ℝ} (hab : a < b) :
    (fun n : ℕ => (n : ℝ) ^ a) =o[atTop] (fun n : ℕ => (n : ℝ) ^ b) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact fun h => False.elim ((Real.rpow_pos_of_pos hn' b).ne' h)
  · have ht := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    simp only [Function.comp_apply]
    rw [← Real.rpow_sub hn']
    congr 1
    ring

private lemma nat_rpow_isBigO {a b : ℝ} (hab : a ≤ b) :
    (fun n : ℕ => (n : ℝ) ^ a) =O[atTop] (fun n : ℕ => (n : ℝ) ^ b) := by
  apply IsBigO.of_bound'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    using Real.rpow_le_rpow_of_exponent_le hn' hab

private lemma nat_rpow_frequently_ne_zero (a : ℝ) :
    ∃ᶠ n : ℕ in atTop, (n : ℝ) ^ a ≠ 0 := by
  apply Filter.Eventually.frequently
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact (Real.rpow_pos_of_pos hn' a).ne'

/-- A little-o upper bound at exponent `β` and arbitrarily close exponent lower
bounds along unbounded sets exclude every nonzero constant-times-power equivalent. -/
theorem no_power_equivalent_of_littleO_and_lower_exponents
    {f : ℕ → ℝ} {β : ℝ}
    (hupper : f =o[atTop] (fun n : ℕ => (n : ℝ) ^ β))
    (hlower : ∀ ε : ℝ, 0 < ε →
      ∃ᶠ n : ℕ in atTop, (n : ℝ) ^ (β - ε) ≤ f n) :
    ¬ ∃ α c : ℝ, c ≠ 0 ∧
      IsEquivalent atTop f (fun n : ℕ => c * (n : ℝ) ^ α) := by
  rintro ⟨α, c, hc, heq⟩
  by_cases hab : α < β
  · let γ : ℝ := (α + β) / 2
    have hag : α < γ := by dsimp [γ]; linarith
    have hgb : γ < β := by dsimp [γ]; linarith
    have hf : f =o[atTop] (fun n : ℕ => (n : ℝ) ^ γ) :=
      heq.trans_isLittleO ((nat_rpow_isLittleO hag).const_mul_left c)
    have hlow : ∃ᶠ n : ℕ in atTop, (n : ℝ) ^ γ ≤ f n := by
      simpa using hlower (β - γ) (sub_pos.mpr hgb)
    obtain ⟨n, hbound, hlow, hn⟩ :=
      ((hf.bound (show (0 : ℝ) < 1 / 2 by norm_num)).and_frequently
        (hlow.and_eventually (eventually_ge_atTop 1))).exists
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hp : 0 < (n : ℝ) ^ γ := Real.rpow_pos_of_pos hn' γ
    simp only [Real.norm_eq_abs, abs_of_pos hp] at hbound
    have := le_abs_self (f n)
    linarith
  · have hle : β ≤ α := le_of_not_gt hab
    have hpow : (fun n : ℕ => (n : ℝ) ^ α) =o[atTop]
        (fun n : ℕ => (n : ℝ) ^ β) :=
      (isLittleO_const_mul_left_iff hc).mp (heq.symm.trans_isLittleO hupper)
    exact isLittleO_irrefl (nat_rpow_frequently_ne_zero β)
      ((nat_rpow_isBigO hle).trans_isLittleO hpow)

/-- Upper bounds at every exponent above `β`, together with an unbounded
normalized lower bound along unbounded sets, exclude a nonzero pure-power
asymptotic. This is the dual obstruction appropriate to a logarithmically
enhanced lower bound. -/
theorem no_power_equivalent_of_upper_exponents_and_unbounded_ratio
    {f : ℕ → ℝ} {β : ℝ}
    (hupper : ∀ ε : ℝ, 0 < ε →
      f =O[atTop] (fun n : ℕ => (n : ℝ) ^ (β + ε)))
    (hlower : ∀ C : ℝ, 0 < C →
      ∃ᶠ n : ℕ in atTop, C * (n : ℝ) ^ β ≤ f n) :
    ¬ ∃ α c : ℝ, c ≠ 0 ∧
      IsEquivalent atTop f (fun n : ℕ => c * (n : ℝ) ^ α) := by
  rintro ⟨α, c, hc, heq⟩
  by_cases hβα : β < α
  · have hε : 0 < (α - β) / 2 := by linarith
    have hpow : (fun n : ℕ => (n : ℝ) ^ (β + (α - β) / 2)) =o[atTop]
        (fun n : ℕ => (n : ℝ) ^ α) :=
      nat_rpow_isLittleO (by linarith)
    have hf : f =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) :=
      (hupper _ hε).trans_isLittleO hpow
    exact isLittleO_irrefl (nat_rpow_frequently_ne_zero α)
      ((isLittleO_const_mul_left_iff hc).mp (heq.symm.trans_isLittleO hf))
  · have hf : f =O[atTop] (fun n : ℕ => (n : ℝ) ^ β) :=
      heq.trans_isBigO ((nat_rpow_isBigO (le_of_not_gt hβα)).const_mul_left c)
    obtain ⟨C, hC⟩ := hf.bound
    have hD : 0 < |C| + 1 := by positivity
    obtain ⟨n, hbound, hlow, hn⟩ :=
      (hC.and_frequently ((hlower (|C| + 1) hD).and_eventually
        (eventually_ge_atTop 1))).exists
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hp : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hn' β
    simp only [Real.norm_eq_abs, abs_of_pos hp] at hbound
    have hCD : C < |C| + 1 := by linarith [le_abs_self C]
    have hmul : C * (n : ℝ) ^ β < (|C| + 1) * (n : ℝ) ^ β :=
      mul_lt_mul_of_pos_right hCD hp
    linarith [le_abs_self (f n)]

/-- Two separated, frequently attained bounds at the same exponent exclude every
positive pure-power equivalent. No global polynomial upper bound is needed.
The graph-theoretic problem is to establish both frequent inequalities for the
ordinary extremal number, rather than for a restricted host class. -/
theorem no_power_equivalent_of_frequent_gap
    {f : ℕ → ℝ} {β a b : ℝ}
    (hfnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ f n)
    (hb : 0 ≤ b) (hba : b < a)
    (hhigh : ∃ᶠ n : ℕ in atTop, a * (n : ℝ) ^ β ≤ f n)
    (hlow : ∃ᶠ n : ℕ in atTop, f n ≤ b * (n : ℝ) ^ β) :
    ¬ ∃ α c : ℝ, 0 < c ∧
      IsEquivalent atTop f (fun n : ℕ => c * (n : ℝ) ^ α) := by
  rintro ⟨α, c, hc, heq⟩
  have ha : 0 < a := lt_of_le_of_lt hb hba
  rcases lt_trichotomy α β with hab | he | hba'
  · have hf : f =o[atTop] (fun n : ℕ => (n : ℝ) ^ β) :=
      heq.trans_isLittleO ((nat_rpow_isLittleO hab).const_mul_left c)
    obtain ⟨n, hbound, hlarge, hn⟩ :=
      ((hf.bound (show 0 < a / 2 by positivity)).and_frequently
        (hhigh.and_eventually (eventually_ge_atTop 1))).exists
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hp : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hn' β
    simp only [Real.norm_eq_abs, abs_of_pos hp] at hbound
    nlinarith [le_abs_self (f n)]
  · subst α
    have herr : (fun n : ℕ => f n - c * (n : ℝ) ^ β) =o[atTop]
        (fun n : ℕ => (n : ℝ) ^ β) := heq.isLittleO.of_const_mul_right
    have hδ : 0 < (a - b) / 4 := by linarith
    by_cases hcm : c ≤ (a + b) / 2
    · obtain ⟨n, hbound, hlarge, hn⟩ :=
        ((herr.bound hδ).and_frequently
          (hhigh.and_eventually (eventually_ge_atTop 1))).exists
      have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hp : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hn' β
      simp only [Real.norm_eq_abs, abs_of_pos hp] at hbound
      have hcm' := mul_le_mul_of_nonneg_right hcm hp.le
      nlinarith [le_abs_self (f n - c * (n : ℝ) ^ β)]
    · obtain ⟨n, hbound, hsmall, hn⟩ :=
        ((herr.bound hδ).and_frequently
          (hlow.and_eventually (eventually_ge_atTop 1))).exists
      have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hp : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hn' β
      simp only [Real.norm_eq_abs, abs_of_pos hp] at hbound
      have hcm' := mul_lt_mul_of_pos_right (lt_of_not_ge hcm) hp
      nlinarith [neg_le_abs (f n - c * (n : ℝ) ^ β)]
  · have hf : (fun n : ℕ => (n : ℝ) ^ β) =o[atTop] f :=
      ((nat_rpow_isLittleO hba').const_mul_right hc.ne').trans_isEquivalent heq.symm
    have hε : 0 < 1 / (b + 1) := by positivity
    obtain ⟨n, hbound, ⟨hsmall, hnonneg⟩, hn⟩ :=
      ((hf.bound hε).and_frequently
        ((hlow.and_eventually hfnonneg).and_eventually
          (eventually_ge_atTop 1))).exists
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hp : 0 < (n : ℝ) ^ β := Real.rpow_pos_of_pos hn' β
    simp only [Real.norm_eq_abs, abs_of_pos hp, abs_of_nonneg hnonneg] at hbound
    have hbound' : (b + 1) * (n : ℝ) ^ β ≤ f n := by
      have hmul := mul_le_mul_of_nonneg_left hbound (show 0 ≤ b + 1 by positivity)
      field_simp at hmul
      nlinarith
    nlinarith

/-- The finite-gap criterion specialized to ordinary graph extremal numbers.
This is conditional: neither frequent inequality is supplied here. -/
theorem extremalNumber_not_power_equivalent_of_frequent_gap
    {q : ℕ} (G : SimpleGraph (Fin q)) {β a b : ℝ}
    (hb : 0 ≤ b) (hba : b < a)
    (hhigh : ∃ᶠ n : ℕ in atTop,
      a * (n : ℝ) ^ β ≤ (SimpleGraph.extremalNumber n G : ℝ))
    (hlow : ∃ᶠ n : ℕ in atTop,
      (SimpleGraph.extremalNumber n G : ℝ) ≤ b * (n : ℝ) ^ β) :
    ¬ ∃ α c : ℝ, α ∈ Set.Ico 1 2 ∧ 0 < c ∧
      IsEquivalent atTop (fun n : ℕ => (SimpleGraph.extremalNumber n G : ℝ))
        (fun n : ℕ => c * (n : ℝ) ^ α) := by
  rintro ⟨α, c, _, hc, heq⟩
  exact no_power_equivalent_of_frequent_gap
    (Eventually.of_forall fun n => Nat.cast_nonneg (SimpleGraph.extremalNumber n G))
    hb hba hhigh hlow ⟨α, c, hc, heq⟩

end Erdos713

#print axioms Erdos713.no_power_equivalent_of_littleO_and_lower_exponents
#print axioms Erdos713.no_power_equivalent_of_upper_exponents_and_unbounded_ratio
#print axioms Erdos713.no_power_equivalent_of_frequent_gap
#print axioms Erdos713.extremalNumber_not_power_equivalent_of_frequent_gap
