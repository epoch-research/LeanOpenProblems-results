import Mathlib
import Submission.Spec
import Submission.Helper9
import Submission.Helper10
import Submission.Helper11
import Submission.Helper12
import Submission.Helper13

open Nat Real intervalIntegral Polynomial Filter Topology Set Metric

lemma J_even_tendsto_zero : Tendsto (fun k : ℕ => J (2 * k)) atTop (nhds 0) := by
  have H_eq : (fun k : ℕ => J (2 * k)) =ᶠ[atTop] (fun k : ℕ => (1/2 : ℝ) * ((2 * (k:ℝ) + 1) * J (2 * k - 1) + J (2 * k - 3))) := by
    apply eventually_atTop.mpr
    use 2
    intro k hk
    have H_rec := J_even_recurrence k hk
    linarith
  have ht1 := J_odd_term_tendsto_zero
  have ht2 : Tendsto (fun k : ℕ => J (2 * k - 3)) atTop (nhds 0) := by
    have eq : (fun k : ℕ => J (2 * k - 3)) =ᶠ[atTop] (fun k : ℕ => J (2 * (k - 2) + 1)) := by
      apply eventually_atTop.mpr
      use 2
      intro k hk
      dsimp
      congr 1
      omega
    have H_sub : Tendsto (fun k : ℕ => J (2 * (k - 2) + 1)) atTop (nhds 0) := by
      have h_sub : Tendsto (fun k : ℕ => k - 2) atTop atTop := tendsto_sub_atTop_nat 2
      exact J_odd_tendsto_zero.comp h_sub
    exact Tendsto.congr' eq.symm H_sub
  have ht_add := Tendsto.add ht1 ht2
  rw [add_zero] at ht_add
  have ht_mul := Tendsto.const_mul (1/2 : ℝ) ht_add
  rw [mul_zero] at ht_mul
  exact Tendsto.congr' H_eq.symm ht_mul

lemma J_tendsto_zero : Tendsto (fun n : ℕ => J n) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have h_even := Metric.tendsto_atTop.mp J_even_tendsto_zero ε hε
  have h_odd := Metric.tendsto_atTop.mp J_odd_tendsto_zero ε hε
  rcases h_even with ⟨N1, hN1⟩
  rcases h_odd with ⟨N2, hN2⟩
  use max (2 * N1) (2 * N2 + 1)
  intro n hn
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk2 : n = 2 * k := by omega
    rw [hk2] at hn ⊢
    have : N1 ≤ k := by omega
    exact hN1 k this
  · have hk2 : n = 2 * k + 1 := by omega
    rw [hk2] at hn ⊢
    have : N2 ≤ k := by omega
    exact hN2 k this
