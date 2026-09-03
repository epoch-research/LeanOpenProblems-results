import FormalConjecturesUtil

/-! A recurrence with nonnegative forward coefficients and positive coefficient
sum is incompatible with a positive linear lower bound. This is a tool for
rejecting fixed potential models, NOT a settlement of Erdős Problem 406. -/
namespace Erdos406BinaryCriticalRecurrence
open scoped BigOperators

lemma linear_lower_min_attained (f : ℕ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hlower : ∀ n : ℕ, a * n - b ≤ f n) :
    ∃ m : ℕ, ∀ n : ℕ, f m ≤ f n := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt ((f 0 + b) / a)
  have hN' : f 0 + b < a * N := by
    have := (div_lt_iff₀ ha).mp hN
    nlinarith
  obtain ⟨m, hm, hmin⟩ := (Finset.range (N+1)).exists_min_image f
    ⟨0, by simp⟩
  refine ⟨m, fun n => ?_⟩
  by_cases hn : n < N+1
  · exact hmin n (Finset.mem_range.mpr hn)
  · have hNn : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
    have hm0 := hmin 0 (by simp)
    have hnlow := hlower n
    nlinarith

/-- The error offset may be arbitrarily large; only the slope must be positive. -/
theorem recurrence_no_positive_linear_lower (d : ℕ) (c₀ : ℝ) (c : Fin d → ℝ)
    (hc : ∀ i, 0 ≤ c i) (hsum : 0 < c₀ + ∑ i, c i)
    (f : ℕ → ℝ)
    (hrec : ∀ n : ℕ, c₀ * f n + ∑ i, c i * f (n + i.val + 1) = 0) :
    ¬ ∃ a b : ℝ, 0 < a ∧ ∀ n : ℕ, a * n - b ≤ f n := by
  rintro ⟨a, b, ha, hlower⟩
  obtain ⟨K, hK⟩ := exists_nat_gt (b/a)
  have hK' : b < a*K := by
    have := (div_lt_iff₀ ha).mp hK
    nlinarith
  let g : ℕ → ℝ := fun n => f (K+n)
  have hg : ∀ n : ℕ, a * n - (b-a*K) ≤ g n := by
    intro n
    have hh := hlower (K+n)
    push_cast at hh
    dsimp [g]
    linarith
  obtain ⟨m, hm⟩ := linear_lower_min_attained g a (b-a*K) ha hg
  have hpos : 0 < g m := by
    have hh := hg m
    have hnonneg : (0 : ℝ) ≤ a*m := mul_nonneg ha.le (Nat.cast_nonneg m)
    linarith
  have hsumle : (∑ i, c i) * g m ≤ ∑ i, c i * g (m+i.val+1) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hm _) (hc i))
  have hr : c₀*g m + ∑ i, c i*g (m+i.val+1) = 0 := by
    simpa only [g, Nat.add_assoc] using hrec (K+m)
  have hcontr := mul_pos hsum hpos
  nlinarith

#print axioms linear_lower_min_attained
#print axioms recurrence_no_positive_linear_lower
end Erdos406BinaryCriticalRecurrence
