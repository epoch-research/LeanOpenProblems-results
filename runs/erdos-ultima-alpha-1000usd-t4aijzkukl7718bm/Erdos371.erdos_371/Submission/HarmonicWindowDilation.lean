import Submission.FixedHarmonicPrimeTransfer

/-! Dilation domination for nonnegative observables of any fixed finite
window. All error terms are explicit and vanish for fixed multipliers and
window lengths. These are harmonic, not natural, endpoint statements. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma prefixMean_shift_zero (F : ℕ → ℝ) (hF : ∀ n, |F n| ≤ 1)
    (hzero : Tendsto (fun N => prefixMean N F) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun N => prefixMean N (fun n => F (n+k))) atTop (𝓝 0) := by
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
    simpa only [Nat.add_right_comm, Nat.add_assoc] using
      prefixMean_succ_zero (fun _ n => F (n+k)) (fun _ n => hF (n+k)) ih

lemma bounded_window_observable_change {A : Type*} [DecidableEq A] {K : ℕ}
    (F : (Fin K → A) → ℝ) (hF : ∀ x, |F x| ≤ 1) (v w : Fin K → A) :
    |F v-F w| ≤ 2*∑ k : Fin K, (if v k ≠ w k then (1 : ℝ) else 0) := by
  classical
  by_cases he : v = w
  · subst w
    simp
  · obtain ⟨k,hk⟩ : ∃ k, v k ≠ w k := Function.ne_iff.mp he
    have hs : (1 : ℝ) ≤ ∑ k : Fin K, (if v k ≠ w k then (1 : ℝ) else 0) := by
      simpa only [if_pos hk] using single_le_sum
        (s := (univ : Finset (Fin K)))
        (fun i _ => by split_ifs <;> norm_num : ∀ i ∈ (univ : Finset (Fin K)),
          0 ≤ (if v i ≠ w i then (1 : ℝ) else 0)) (mem_univ k)
    exact (abs_sub _ _).trans (by linarith [hF v,hF w])

lemma harmonicMean_fin_sum {ι : Type*} [Fintype ι] (N : ℕ) (F : ι → ℕ → ℝ) :
    harmonicMean N (fun n => ∑ k, F k n) = ∑ k, harmonicMean N (F k) := by
  simp only [harmonicMean,sum_div]
  rw [sum_comm]

noncomputable def windowDilationBudget {A : Type*} (N p K : ℕ) (L : ℕ → A) : ℝ :=
  p/(harmonic (N+1) : ℝ)+2*∑ k : Fin K,
    harmonicMean (N+1) (fun n => labelDilationDefect p L (n+k))

/-- Restriction to the residue zero modulo p becomes dilation of the fixed
window, with one defect for each window coordinate. -/
lemma harmonic_window_dilation_error {A : Type*} (N p K : ℕ) (hp : 0 < p)
    (L : ℕ → A) (F : (Fin K → A) → ℝ) (hF : ∀ x, |F x| ≤ 1) :
    |p*harmonicMean (N+1) (fun n => if p ∣ n then F (fun k => L (n+p*k)) else 0)-
      harmonicMean (N+1) (fun n => F (fun k => L (n+k)))| ≤ windowDilationBudget N p K L := by
  classical
  let V (n : ℕ) := F (fun k => L (p*(n+k)))
  let W (n : ℕ) := F (fun k => L (n+k))
  let B : ℝ := p*harmonicMean (N+1)
    (fun n => if p ∣ n then F (fun k => L (n+p*k)) else 0)
  have hd : B = (∑ n ∈ Icc 1 ((N+1)/p), V n/(n : ℝ))/(harmonic (N+1) : ℝ) := by
    dsimp [B,harmonicMean]
    simp only [ite_div,zero_div]
    rw [← mul_div_assoc,harmonic_dilation_sum p (N+1) hp]
    congr 1
    apply sum_congr rfl
    intro n hn
    dsimp only [V]
    congr 2
    funext k
    rw [mul_add]
  have htail : |B-harmonicMean (N+1) V| ≤ p/(harmonic (N+1) : ℝ) := by
    rw [hd,harmonicMean,← sub_div,abs_div,abs_of_pos (harmonic_real_pos N),abs_sub_comm]
    exact div_le_div_of_nonneg_right (harmonic_div_endpoint_bound p (N+1) hp V (fun n => hF _))
      (harmonic_real_pos N).le
  have hpoint (n : ℕ) : |V n-W n| ≤ 2*∑ k : Fin K, labelDilationDefect p L (n+k) := by
    exact bounded_window_observable_change F hF _ _
  have hdiff : |harmonicMean (N+1) V-harmonicMean (N+1) W| ≤
      2*∑ k : Fin K, harmonicMean (N+1) (fun n => labelDilationDefect p L (n+k)) := by
    apply (harmonicMean_abs_difference_le N V W).trans
    have hh := harmonicMean_mono N _ _ hpoint
    simpa only [harmonicMean_const_mul,harmonicMean_fin_sum] using hh
  change |B-harmonicMean (N+1) W| ≤ _
  exact (abs_sub_le B (harmonicMean (N+1) V) (harmonicMean (N+1) W)).trans
    (add_le_add htail hdiff)

lemma windowDilationBudget_zero {A : Type*} (p K : ℕ) (L : ℕ → A)
    (hL : Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0)) :
    Tendsto (fun N => windowDilationBudget N p K L) atTop (𝓝 0) := by
  have hd (k : Fin K) : Tendsto (fun N => harmonicMean (N+1)
      (fun n => labelDilationDefect p L (n+k))) atTop (𝓝 0) :=
    harmonicMean_zero_of_prefixMean_zero _
      (fun n => labelDilationDefect_abs_le p L (n+k))
      (prefixMean_shift_zero _ (labelDilationDefect_abs_le p L) hL k)
  have hs := tendsto_finset_sum univ (fun k _ => hd k)
  have ht : Tendsto (fun N : ℕ => (p : ℝ)/(harmonic (N+1) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop harmonic_real_tendsto
  simpa only [windowDilationBudget,sum_const_zero,mul_zero,add_zero] using ht.add (hs.const_mul 2)

lemma harmonic_window_dilation_le {A : Type*} (N p K : ℕ) (hp : 0 < p)
    (L : ℕ → A) (F : (Fin K → A) → ℝ) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    harmonicMean (N+1) (fun n => F (fun k => L (n+k))) ≤
      p*harmonicMean (N+1) (fun n => F (fun k => L (n+p*k)))+windowDilationBudget N p K L := by
  classical
  have he := (abs_le.mp (harmonic_window_dilation_error N p K hp L F
    (fun x => by rw [abs_of_nonneg (hF x).1]; exact (hF x).2))).1
  have hm := harmonicMean_mono N
    (fun n => if p ∣ n then F (fun k => L (n+p*k)) else 0)
    (fun n => F (fun k => L (n+p*k))) (fun n => by
      dsimp only
      split_ifs
      · exact le_rfl
      · exact (hF _).1)
  have hpR : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  linarith [mul_le_mul_of_nonneg_left hm hpR]

/-- Every simultaneous harmonic limit satisfies dilation domination on fixed
nonnegative cylinder observables. No stationary-measure construction is
assumed, and the same endpoint subsequence is required in both limits. -/
theorem harmonic_window_dilation_limit_le {A : Type*} (p K : ℕ) (hp : 0 < p)
    (L : ℕ → A) (F : (Fin K → A) → ℝ) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1)
    (hL : Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : Tendsto D atTop atTop) (a b : ℝ)
    (ha : Tendsto (fun j => harmonicMean (D j+1) (fun n => F (fun k => L (n+k)))) atTop (𝓝 a))
    (hb : Tendsto (fun j => harmonicMean (D j+1) (fun n => F (fun k => L (n+p*k)))) atTop (𝓝 b)) :
    a ≤ p*b := by
  have hh := le_of_tendsto_of_tendsto' ha
    ((hb.const_mul (p : ℝ)).add ((windowDilationBudget_zero p K L hL).comp hD))
    (fun j => harmonic_window_dilation_le (D j) p K hp L F hF)
  simpa only [add_zero] using hh

#print axioms harmonic_window_dilation_limit_le
end Erdos371.FiniteInformation
