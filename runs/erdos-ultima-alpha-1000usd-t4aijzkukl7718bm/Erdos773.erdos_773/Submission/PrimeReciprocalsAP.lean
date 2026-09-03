import FormalConjecturesUtil

/-!
Reciprocal-prime divergence in a reduced residue class, obtained from the
von Mangoldt L-series pole by dominated convergence.
This is an auxiliary analytic result, not a settlement of Erdős 773.
-/

namespace Erdos773

open Filter Topology ArithmeticFunction
open ArithmeticFunction.vonMangoldt

lemma small_exponent_log_bound {n t : ℝ} (hn : 0 < n) :
    t * Real.log n ≤ n ^ t := by
  rw [Real.rpow_def_of_pos hn]
  have h := Real.add_one_le_exp (Real.log n * t)
  nlinarith

lemma prime_log_rpow_bound {n : ℕ} (hn : n.Prime) {t : ℝ} :
    t * (Real.log n / (n : ℝ) ^ (1 + t)) ≤ 1 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.pos
  rw [Real.rpow_add hn0, Real.rpow_one]
  have h := small_exponent_log_bound (t := t) hn0
  apply (le_div_iff₀ hn0).mpr
  have hpow : (0 : ℝ) < (n : ℝ) ^ t := Real.rpow_pos_of_pos hn0 _
  field_simp
  nlinarith

lemma not_summable_prime_reciprocals_residue_class {q : ℕ} [NeZero q]
    {a : ZMod q} (ha : IsUnit a) :
    ¬ Summable (fun n : ℕ => if n.Prime ∧ (n : ZMod q) = a then (1 : ℝ) / n else 0) := by
  classical
  intro hsum
  let t : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have ht0 (k : ℕ) : 0 < t k := by dsimp [t]; positivity
  have ht1 (k : ℕ) : t k ≤ 1 := by
    dsimp [t]
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let b : ℕ → ℝ := fun n =>
    (if n.Prime ∧ (n : ZMod q) = a then (1 : ℝ) / n else 0) +
      (if n.Prime then 0 else residueClass a n) / n
  have hb : Summable b := hsum.add (summable_residueClass_non_primes_div a)
  let f : ℕ → ℕ → ℝ := fun k n => t k * (residueClass a n / (n : ℝ) ^ (1 + t k))
  have hf0 (n : ℕ) : Tendsto (fun k => f k n) atTop (𝓝 0) := by
    by_cases hn : n = 0
    · subst n
      simpa [f] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpow : Tendsto (fun k => (n : ℝ) ^ (1 + t k)) atTop (𝓝 (n : ℝ)) := by
      simpa using (Real.continuousAt_const_rpow hn0.ne').tendsto.comp
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add ht)
    simpa [f] using ht.mul (tendsto_const_nhds.div hpow hn0.ne')
  have hfb (k n : ℕ) : ‖f k n‖ ≤ b n := by
    have hfnonneg : 0 ≤ f k n := by
      exact mul_nonneg (ht0 k).le (div_nonneg (residueClass_nonneg a n)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    rw [Real.norm_eq_abs, abs_of_nonneg hfnonneg]
    by_cases hp : n.Prime
    · by_cases hna : (n : ZMod q) = a
      · simpa [f, b, hp, hna, residueClass, Set.indicator_apply,
          vonMangoldt_apply_prime hp] using prime_log_rpow_bound (t := t k) hp
      · simp [f, b, hp, hna, residueClass, Set.indicator_apply]
    · simp only [b, hp, false_and, ↓reduceIte, zero_add]
      by_cases hn : n = 0
      · subst n
        simp [f]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hn0 : (0 : ℝ) < n := by linarith
      calc
        f k n ≤ residueClass a n / (n : ℝ) ^ (1 + t k) := by
          dsimp [f]
          exact mul_le_of_le_one_left (by positivity [residueClass_nonneg a n]) (ht1 k)
        _ ≤ residueClass a n / n := by
          apply div_le_div_of_nonneg_left (residueClass_nonneg a n) hn0
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le hn1 (show (1 : ℝ) ≤ 1 + t k by linarith [ht0 k])
  have hf : Tendsto (fun k => ∑' n, f k n) atTop (𝓝 0) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hb hf0
      (Eventually.of_forall fun k n => hfb k n)
  obtain ⟨C, hC⟩ := LSeries_residueClass_lower_bound ha
  have hlow (k : ℕ) : (q.totient : ℝ)⁻¹ ≤ (∑' n, f k n) + C * t k := by
    have hx : 1 + t k ∈ Set.Ioc (1 : ℝ) 2 := ⟨by linarith [ht0 k], by linarith [ht1 k]⟩
    have h := hC hx
    rw [add_sub_cancel_left] at h
    have h' := mul_le_mul_of_nonneg_right h (ht0 k).le
    rw [sub_mul, div_mul_cancel₀ _ (ht0 k).ne'] at h'
    dsimp [f]
    rw [tsum_mul_left]
    nlinarith
  have hz : (q.totient : ℝ)⁻¹ ≤ 0 := by
    apply ge_of_tendsto (by simpa using hf.add (ht.const_mul C))
    exact Eventually.of_forall (fun k => by simpa [t] using hlow k)
  have hp : 0 < (q.totient : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast q.totient.pos_of_neZero)
  linarith

#print axioms not_summable_prime_reciprocals_residue_class

end Erdos773
