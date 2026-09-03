import Submission.BuchstabSelbergSource

/-! Monotonicity in divisor level, used to extend rigorous values at finitely
many logarithmic nodes to every intervening parameter value. These statements
concern main terms only, not the separately propagated error budgets. -/
namespace Erdos970.RecursiveSieve.Buchstab
open Finset Real FiniteSelberg

lemma lowerStep_level_monotone (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i)
    (keep : ℕ → ℝ → Prop) (hkeep : ∀ k D E, D ≤ E → keep k D → keep k E)
    (U : ℕ → ℝ → ℝ) (hU : ∀ k, Antitone (U k)) (k : ℕ) :
    Monotone (lowerStep q keep U k) := by
  classical
  intro D E hDE
  by_cases hk : keep k D
  · unfold lowerStep
    rw [if_pos hk, if_pos (hkeep k D E hDE hk)]
    apply max_le_max_left
    apply sub_le_sub_left
    apply sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (hU i.val (mul_le_mul_of_nonneg_right hDE (hq i.val))) (hq i.val)
  · unfold lowerStep
    rw [if_neg hk]
    split_ifs
    · exact le_max_left _ _
    · rfl

theorem upperMain_level_antitone (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i)
    (keep : ℕ → ℝ → Prop) (hkeep : ∀ k D E, D ≤ E → keep k D → keep k E)
    (base : ℕ → ℝ → ℝ) (hbase : ∀ k, Antitone (base k)) (n k : ℕ) :
    Antitone (upperMain q keep base n k) := by
  induction n generalizing k with
  | zero => exact hbase k
  | succ n ih =>
    intro D E hDE
    apply min_le_min (ih k hDE)
    apply sub_le_sub_left
    apply sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (lowerStep_level_monotone q hq keep hkeep (upperMain q keep base n) ih i.val
        (mul_le_mul_of_nonneg_right hDE (hq i.val))) (hq i.val)

lemma inverse_normalizer_antitone {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (S T : Finset (Finset ι)) (hS : S.Nonempty) (hST : S ⊆ T) :
    1/normalizer q T ≤ 1/normalizer q S := by
  apply one_div_le_one_div_of_le (normalizer_pos q hq S hS)
  exact sum_le_sum_of_subset_of_nonneg hST
    (fun U _ _ => (one_div_pos.mpr (variance_pos q hq U)).le)

lemma density_le_inverse_normalizer {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (S : Finset (Finset ι)) (hS : S.Nonempty) :
    (∏ i, (1-q i)) ≤ 1/normalizer q S := by
  have hfull : normalizer q univ = 1/(∏ i, (1-q i)) := by
    simp only [normalizer, ← weight_eq_inverse_variance, sum_weight]
    rw [one_div, ← prod_inv_distrib]
    apply prod_congr rfl
    intro i hi
    have hd : 1-q i ≠ 0 := (sub_pos.mpr (hq i).2).ne'
    field_simp
    ring
  have hh := inverse_normalizer_antitone q hq S univ hS (subset_univ _)
  rw [hfull] at hh
  simpa only [one_div, inv_inv] using hh

lemma selbergCutoff_monotone : Monotone selbergCutoff := by
  intro D E hDE
  exact max_le_max_left 1 (Nat.floor_le_floor (sqrt_le_sqrt hDE))

lemma selbergBase_antitone (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (k : ℕ) :
    Antitone (selbergBase p k) := by
  intro D E hDE
  have hq (i : Fin k) : 0 < 1/(p i.val : ℝ) ∧ 1/(p i.val : ℝ) < 1 := by
    have hi : (1 : ℝ) < p i.val := by exact_mod_cast (hp i.val).one_lt
    exact ⟨by positivity, (div_lt_one (by linarith)).mpr hi⟩
  apply inverse_normalizer_antitone _ hq _ _
    (divisorSupport_nonempty _ _ (by unfold selbergCutoff; omega))
  intro T hT
  rw [mem_divisorSupport] at hT ⊢
  exact hT.trans (selbergCutoff_monotone hDE)

lemma selbergBase_density (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (k : ℕ) (D : ℝ) :
    prefixDensity (fun i => 1/(p i : ℝ)) k ≤ selbergBase p k D := by
  have hq (i : Fin k) : 0 < 1/(p i.val : ℝ) ∧ 1/(p i.val : ℝ) < 1 := by
    have hi : (1 : ℝ) < p i.val := by exact_mod_cast (hp i.val).one_lt
    exact ⟨by positivity, (div_lt_one (by linarith)).mpr hi⟩
  have hh := density_le_inverse_normalizer (fun i : Fin k => 1/(p i.val : ℝ)) hq
    (divisorSupport (fun i : Fin k => p i.val) (selbergCutoff D))
    (divisorSupport_nonempty _ _ (by unfold selbergCutoff; omega))
  rw [Fin.prod_univ_eq_prod_range (fun i => 1-1/(p i : ℝ)) k] at hh
  exact hh

/-- All canonical refined upper main terms decrease with level. -/
theorem selberg_upperMain_antitone (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (n k : ℕ) :
    Antitone (upperMain (fun i => 1/(p i : ℝ)) (primeKeep p) (selbergBase p) n k) :=
  upperMain_level_antitone _ (fun i => by positivity) _
    (fun k D E hDE hk => hk.trans hDE) _ (selbergBase_antitone p hp) n k

/-- All canonical refined lower main terms increase with level. -/
theorem selberg_lowerStep_monotone (p : ℕ → ℕ) (hp : ∀ i, (p i).Prime) (n k : ℕ) :
    Monotone (lowerStep (fun i => 1/(p i : ℝ)) (primeKeep p)
      (upperMain (fun i => 1/(p i : ℝ)) (primeKeep p) (selbergBase p) n) k) :=
  lowerStep_level_monotone _ (fun i => by positivity) _
    (fun k D E hDE hk => hk.trans hDE) _ (selberg_upperMain_antitone p hp n) k

#print axioms selbergBase_density
#print axioms selberg_upperMain_antitone
#print axioms selberg_lowerStep_monotone
end Erdos970.RecursiveSieve.Buchstab
