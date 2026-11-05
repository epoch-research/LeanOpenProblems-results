import FormalConjecturesUtil

/-!
# Reciprocal sums and finite base-4 shells

The positive natural numbers are split into the finite intervals
`[4 ^ j, 4 ^ (j + 1))`, for `j : ℕ`. Uniform bounds for the sums on these
shells give uniform bounds for all finite reciprocal sums, and hence
summability. No arithmetic-progression hypothesis is used.
-/

namespace Erdos3Aux

open scoped BigOperators

/-- The `j`-th base-4 shell. Its members are positive natural numbers. -/
def fourShell (j : ℕ) : Finset ℕ :=
  Finset.Ico (4 ^ j) (4 ^ (j + 1))

/-- The part of a set of natural numbers in the `j`-th base-4 shell. -/
noncomputable def fourShellIn (A : Set ℕ) (j : ℕ) : Finset ℕ := by
  classical
  exact (fourShell j).filter (fun n ↦ n ∈ A)

/-- A finite reciprocal sum over the members of `A` in `s`.
The term at zero is zero, by the convention for division in `ℝ`. -/
noncomputable def reciprocalSum (A : Set ℕ) (s : Finset ℕ) : ℝ := by
  classical
  exact ∑ n ∈ s.filter (fun n ↦ n ∈ A), 1 / (n : ℝ)

/-- The reciprocal sum of `A` on a single finite base-4 shell. -/
noncomputable def reciprocalShellSum (A : Set ℕ) (j : ℕ) : ℝ :=
  reciprocalSum A (fourShell j)

@[simp] theorem mem_fourShell {j n : ℕ} :
    n ∈ fourShell j ↔ 4 ^ j ≤ n ∧ n < 4 ^ (j + 1) := by
  simp [fourShell]

@[simp] theorem mem_fourShellIn {A : Set ℕ} {j n : ℕ} :
    n ∈ fourShellIn A j ↔ n ∈ A ∧ 4 ^ j ≤ n ∧ n < 4 ^ (j + 1) := by
  classical
  simp [fourShellIn, and_comm]

theorem fourShell_pos {j n : ℕ} (hn : n ∈ fourShell j) : 0 < n :=
  (Nat.pow_pos (by norm_num : 0 < 4)).trans_le (mem_fourShell.mp hn).1

/-- The shells telescope to an initial interval, with the zero term separated out. -/
theorem sum_range_four_pow (f : ℕ → ℝ) (k : ℕ) :
    (∑ n ∈ Finset.range (4 ^ k), f n) =
      f 0 + ∑ j ∈ Finset.range k, ∑ n ∈ fourShell j, f n := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hpow : 4 ^ k ≤ (4 : ℕ) ^ (k + 1) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)
      rw [← Finset.sum_range_add_sum_Ico f hpow, ih, Finset.sum_range_succ]
      simp only [fourShell, add_assoc]

/-- A summable nonnegative majorant for shell sums bounds every initial sum.
The zero term is harmless and is retained explicitly in this general lemma. -/
theorem sum_range_le_of_fourShell_bounds {f b : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hb : ∀ j, 0 ≤ b j) (hbs : Summable b)
    (hbound : ∀ j, (∑ n ∈ fourShell j, f n) ≤ b j) (N : ℕ) :
    (∑ n ∈ Finset.range N, f n) ≤ f 0 + ∑' j, b j := by
  calc
    (∑ n ∈ Finset.range N, f n) ≤ ∑ n ∈ Finset.range (4 ^ N), f n :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.lt_pow_self (by norm_num : 1 < 4)).le)
        (fun n _ _ ↦ hf n)
    _ = f 0 + ∑ j ∈ Finset.range N, ∑ n ∈ fourShell j, f n :=
      sum_range_four_pow f N
    _ ≤ f 0 + ∑ j ∈ Finset.range N, b j :=
      add_le_add_right (Finset.sum_le_sum (fun j _ ↦ hbound j)) _
    _ ≤ f 0 + ∑' j, b j :=
      add_le_add_right (hbs.sum_le_tsum (Finset.range N) (fun j _ ↦ hb j)) _

/-- General nonnegative shell criterion, proved from bounded initial sums. -/
theorem summable_of_fourShell_bounds {f b : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hb : ∀ j, 0 ≤ b j) (hbs : Summable b)
    (hbound : ∀ j, (∑ n ∈ fourShell j, f n) ≤ b j) : Summable f :=
  summable_of_sum_range_le hf (sum_range_le_of_fourShell_bounds hf hb hbs hbound)

/-- Rewriting a finite reciprocal sum as a sum of an indicator function. -/
theorem reciprocalSum_eq_indicator (A : Set ℕ) (s : Finset ℕ) :
    reciprocalSum A s = ∑ n ∈ s, A.indicator (fun n ↦ 1 / (n : ℝ)) n := by
  classical
  simp only [reciprocalSum, Finset.sum_filter, Set.indicator_apply]

theorem reciprocal_indicator_nonneg (A : Set ℕ) (n : ℕ) :
    0 ≤ A.indicator (fun n ↦ 1 / (n : ℝ)) n :=
  Set.indicator_nonneg (fun n _ ↦ one_div_nonneg.mpr (Nat.cast_nonneg n)) n

@[simp] theorem reciprocal_indicator_zero (A : Set ℕ) :
    A.indicator (fun n ↦ 1 / (n : ℝ)) 0 = 0 := by
  apply Set.indicator_apply_eq_zero.mpr
  intro _
  simp

theorem reciprocalShellSum_nonneg (A : Set ℕ) (j : ℕ) :
    0 ≤ reciprocalShellSum A j := by
  rw [reciprocalShellSum, reciprocalSum_eq_indicator]
  exact Finset.sum_nonneg (fun n _ ↦ reciprocal_indicator_nonneg A n)

/-- Every partial reciprocal sum is at most the sum of the shell majorant. -/
theorem reciprocal_partial_sum_le {A : Set ℕ} {b : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ b j) (hbs : Summable b)
    (hbound : ∀ j, reciprocalShellSum A j ≤ b j) (N : ℕ) :
    reciprocalSum A (Finset.range N) ≤ ∑' j, b j := by
  rw [reciprocalSum_eq_indicator]
  have h := sum_range_le_of_fourShell_bounds (reciprocal_indicator_nonneg A) hb hbs
    (fun j ↦ by simpa only [reciprocalShellSum, reciprocalSum_eq_indicator] using hbound j) N
  simpa only [reciprocal_indicator_zero, zero_add] using h

/-- The same bound holds for an arbitrary finite subsum, not just an initial interval. -/
theorem reciprocal_finite_sum_le {A : Set ℕ} {b : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ b j) (hbs : Summable b)
    (hbound : ∀ j, reciprocalShellSum A j ≤ b j) (s : Finset ℕ) :
    reciprocalSum A s ≤ ∑' j, b j := by
  calc
    reciprocalSum A s ≤ reciprocalSum A (Finset.range (s.sup id).succ) := by
      rw [reciprocalSum_eq_indicator, reciprocalSum_eq_indicator]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_range_sup_succ s)
        (fun n _ _ ↦ reciprocal_indicator_nonneg A n)
    _ ≤ ∑' j, b j := reciprocal_partial_sum_le hb hbs hbound _

/-- Main reciprocal shell criterion. The hypotheses concern only the finite shells
and a nonnegative summable real-valued majorant; membership of zero in `A` is allowed. -/
theorem summable_reciprocal_of_shell_bound {A : Set ℕ} {b : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ b j) (hbs : Summable b)
    (hbound : ∀ j, reciprocalShellSum A j ≤ b j) :
    Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  apply (summable_subtype_iff_indicator (s := A) (f := fun n : ℕ ↦ 1 / (n : ℝ))).mpr
  exact summable_of_fourShell_bounds (reciprocal_indicator_nonneg A) hb hbs
    (fun j ↦ by simpa only [reciprocalShellSum, reciprocalSum_eq_indicator] using hbound j)

/-- Quantitative infinite-sum bound accompanying the summability criterion. -/
theorem tsum_reciprocal_le_of_shell_bound {A : Set ℕ} {b : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ b j) (hbs : Summable b)
    (hbound : ∀ j, reciprocalShellSum A j ≤ b j) :
    (∑' a : A, 1 / (a : ℝ)) ≤ ∑' j, b j := by
  rw [tsum_subtype A (fun n : ℕ ↦ 1 / (n : ℝ))]
  exact Real.tsum_le_of_sum_range_le (reciprocal_indicator_nonneg A)
    (fun N ↦ by simpa only [reciprocalSum_eq_indicator] using
      reciprocal_partial_sum_le hb hbs hbound N)

/-- Finite exceptional shells do not affect the shell criterion. -/
theorem summable_reciprocal_of_eventually_shell_bound {A : Set ℕ} {b : ℕ → ℝ}
    (hbs : Summable b)
    (hbound : ∀ᶠ j in Filter.atTop, reciprocalShellSum A j ≤ b j) :
    Summable (fun a : A ↦ 1 / (a : ℝ)) := by
  have hs : Summable (reciprocalShellSum A) :=
    hbs.of_norm_bounded_eventually_nat (hbound.mono fun j hj ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (reciprocalShellSum_nonneg A j)] using hj)
  exact summable_reciprocal_of_shell_bound (reciprocalShellSum_nonneg A) hs (fun _ ↦ le_rfl)

/-- A nonsummable reciprocal series must exceed every summable shell majorant
on arbitrarily large shell indices. No sign assumption on the majorant is needed here. -/
theorem frequently_shell_bound_of_not_summable {A : Set ℕ} {b : ℕ → ℝ}
    (hA : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) (hbs : Summable b) :
    ∃ᶠ j in Filter.atTop, b j < reciprocalShellSum A j := by
  by_contra h
  apply hA
  exact summable_reciprocal_of_eventually_shell_bound hbs
    ((Filter.not_frequently.mp h).mono fun _ hj ↦ le_of_not_gt hj)

/-- On the `j`-th shell, each reciprocal is at most `1 / 4 ^ j`. -/
theorem reciprocalShellSum_le_card_div (A : Set ℕ) (j : ℕ) :
    reciprocalShellSum A j ≤ ((fourShellIn A j).card : ℝ) / (4 : ℝ) ^ j := by
  change (∑ n ∈ fourShellIn A j, 1 / (n : ℝ)) ≤ _
  have h := Finset.sum_le_card_nsmul (fourShellIn A j)
    (fun n ↦ 1 / (n : ℝ)) (1 / (4 : ℝ) ^ j) (fun n hn ↦ by
      apply one_div_le_one_div_of_le (pow_pos (by norm_num) j)
      exact_mod_cast (mem_fourShellIn.mp hn).2.1)
  simpa only [nsmul_eq_mul, mul_one_div] using h

/-- General infinitely-often lower cardinality bound supplied by nonsummability. -/
theorem frequently_fourShell_card_of_not_summable {A : Set ℕ} {b : ℕ → ℝ}
    (hA : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) (hbs : Summable b) :
    ∃ᶠ j in Filter.atTop, b j * (4 : ℝ) ^ j < ((fourShellIn A j).card : ℝ) := by
  exact (frequently_shell_bound_of_not_summable hA hbs).mono fun j hj ↦
    (lt_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 4) j)).mp
      (hj.trans_le (reciprocalShellSum_le_card_div A j))

/-- A p-series majorant gives the expected `4 ^ j / (j + 1) ^ γ` shell cardinality
bound at arbitrarily large indices whenever `γ > 1`. -/
theorem frequently_fourShell_card_rpow_of_not_summable {A : Set ℕ} {γ : ℝ}
    (hA : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) (hγ : 1 < γ) :
    ∃ᶠ j in Filter.atTop,
      (4 : ℝ) ^ j / ((j + 1 : ℕ) : ℝ) ^ γ < ((fourShellIn A j).card : ℝ) := by
  have hs : Summable (fun j : ℕ ↦ 1 / ((j + 1 : ℕ) : ℝ) ^ γ) :=
    (summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ) ^ γ) 1).mpr
      (Real.summable_one_div_nat_rpow.mpr hγ)
  simpa only [one_div, div_eq_mul_inv, mul_one, mul_comm] using
    frequently_fourShell_card_of_not_summable hA hs

/-- Number of positive members of `A` strictly below `N`. -/
noncomputable def positiveCount (A : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.Ico 1 N).filter (fun n ↦ n ∈ A)).card

theorem fourShellIn_card_le_positiveCount (A : Set ℕ) (j : ℕ) :
    (fourShellIn A j).card ≤ positiveCount A (4 ^ (j + 1)) := by
  classical
  apply Finset.card_le_card
  intro n hn
  have h := mem_fourShellIn.mp hn
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
    ⟨fourShell_pos (mem_fourShell.mpr h.2), h.2.2⟩, h.1⟩

/-- A nonsummable reciprocal series has more than `N / (log N) ^ γ` positive
members below `N` for arbitrarily large `N`, for every real exponent `γ > 1`. -/
theorem frequently_positiveCount_gt_div_log_rpow_of_not_summable
    {A : Set ℕ} {γ : ℝ}
    (hA : ¬ Summable (fun a : A ↦ 1 / (a : ℝ))) (hγ : 1 < γ) :
    ∃ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) / (Real.log (N : ℝ)) ^ γ < (positiveCount A N : ℝ) := by
  let c : ℝ := 4 / (Real.log 4) ^ γ
  have hs : Summable (fun j : ℕ ↦ c * (1 / ((j + 1 : ℕ) : ℝ) ^ γ)) :=
    ((summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ) ^ γ) 1).mpr
      (Real.summable_one_div_nat_rpow.mpr hγ)).mul_left c
  have hf := frequently_fourShell_card_of_not_summable hA hs
  apply Filter.frequently_atTop.mpr
  intro N₀
  obtain ⟨j, hj, hcard⟩ := Filter.frequently_atTop.mp hf N₀
  refine ⟨4 ^ (j + 1), hj.trans ((Nat.le_succ j).trans
    (Nat.lt_pow_self (by norm_num : 1 < 4)).le), ?_⟩
  have heq : c * (1 / ((j + 1 : ℕ) : ℝ) ^ γ) * (4 : ℝ) ^ j =
      ((4 ^ (j + 1) : ℕ) : ℝ) / (Real.log ((4 ^ (j + 1) : ℕ) : ℝ)) ^ γ := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow,
      Real.mul_rpow (Nat.cast_nonneg (j + 1)) (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 4)))]
    simp only [c, pow_succ, div_eq_mul_inv, one_mul, mul_inv_rev]
    ring
  rw [← heq]
  exact hcard.trans_le (by exact_mod_cast fourShellIn_card_le_positiveCount A j)

end Erdos3Aux
