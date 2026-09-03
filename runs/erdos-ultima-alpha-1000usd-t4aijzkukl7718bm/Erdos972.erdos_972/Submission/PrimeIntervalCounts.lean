import Submission.ChebyshevPNT

/-! Prime counts in dyadic intervals, deduced from qualitative Chebyshev PNT. -/
namespace Erdos972PrimeIntervalCounts

open Finset Filter
open scoped Topology
open Erdos972ChebyshevPNT

noncomputable def primesBetween (a b : ℕ) : Finset ℕ := (Ioc a b).filter Nat.Prime

lemma mem_primesBetween {a b p : ℕ} : p ∈ primesBetween a b ↔ a < p ∧ p ≤ b ∧ p.Prime := by
  simp only [primesBetween, mem_filter, mem_Ioc, and_assoc]

lemma theta_interval_sum {a b : ℕ} (hab : a ≤ b) :
    (∑ p ∈ primesBetween a b, Real.log p) = Chebyshev.theta b-Chebyshev.theta a := by
  have hh := sum_Ioc_consecutive (fun p : ℕ => if p.Prime then Real.log p else 0) (Nat.zero_le a) hab
  simp only [Chebyshev.theta, Nat.floor_natCast, primesBetween, sum_filter]
  linarith only [hh]

lemma theta_interval_le_card_log {a b : ℕ} (hab : a ≤ b) :
    Chebyshev.theta b-Chebyshev.theta a ≤ (primesBetween a b).card*Real.log b := by
  rw [← theta_interval_sum hab]
  calc
    _ ≤ ∑ p ∈ primesBetween a b, Real.log b := by
      apply sum_le_sum
      intro p hp
      obtain ⟨_, hpb, hprime⟩ := mem_primesBetween.mp hp
      exact Real.log_le_log (Nat.cast_pos.mpr hprime.pos) (Nat.cast_le.mpr hpb)
    _ = _ := by simp

lemma eventually_prime_interval_counts :
    ∀ᶠ x : ℕ in atTop, 1 < x ∧
      (x : ℝ)/(2*Real.log x) ≤ (primesBetween 0 x).card ∧
      (x : ℝ)/(2*Real.log (2*x : ℕ)) ≤ (primesBetween x (2*x)).card := by
  have hi := (eventually_theta_interval_lower (a := 1) (b := 2) (by norm_num) (by norm_num))
  have hθ := (tendsto_order.mp (theta_div_self_tendsto.comp tendsto_natCast_atTop_atTop)).1
    (1/2) (by norm_num : (1/2 : ℝ) < 1)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hi, hθ, eventually_ge_atTop (2 : ℕ)] with x hi hθ hx
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hx)
  have hx1 : (1 : ℝ) < x := by exact_mod_cast hx
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hlog2 : 0 < Real.log (2*x : ℕ) := Real.log_pos (by push_cast; linarith only [hx1])
  refine ⟨by omega, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < 2*Real.log x)).mpr
    have hh := theta_interval_le_card_log (Nat.zero_le x)
    simp only [Nat.cast_zero, Chebyshev.theta, Nat.floor_zero, Ioc_self, filter_empty, sum_empty, sub_zero] at hh
    have hθ' := (lt_div_iff₀ hx0).mp hθ
    change (1/2 : ℝ)*(x : ℝ) < Chebyshev.theta x at hθ'
    change Chebyshev.theta x ≤ (primesBetween 0 x).card*Real.log x at hh
    nlinarith only [hθ', hh]
  · apply (div_le_iff₀ (by positivity : 0 < 2*Real.log (2*x : ℕ))).mpr
    have hh := theta_interval_le_card_log (show x ≤ 2*x by omega)
    norm_num only [sub_self, sub_zero, one_mul, Nat.cast_ofNat] at hi
    have hi' : (x : ℝ)/2 ≤ Chebyshev.theta (2*x : ℕ)-Chebyshev.theta x := by
      convert hi using 1 <;> push_cast <;> ring
    nlinarith only [hi', hh]

#print axioms eventually_prime_interval_counts

end Erdos972PrimeIntervalCounts
