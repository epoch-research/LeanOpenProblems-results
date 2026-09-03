import Submission.Development

/-!
Auxiliary complete-monotonicity results for factorial-power tails.
These are not a proof or disproof of the conjecture in Spec.lean.
-/

namespace CompletelyMonotoneDifferences

noncomputable def diff : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, f, n => f n
  | r + 1, f, n => diff r f n - diff r f (n + 1)

@[simp] lemma diff_zero (f : ℕ → ℝ) (n : ℕ) : diff 0 f n = f n := rfl
@[simp] lemma diff_succ (r : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    diff (r + 1) f n = diff r f n - diff r f (n + 1) := rfl

lemma diff_add (r : ℕ) (f g : ℕ → ℝ) (n : ℕ) :
    diff r (fun k => f k + g k) n = diff r f n + diff r g n := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih => simp only [diff_succ, ih]; ring

lemma diff_sub (r : ℕ) (f g : ℕ → ℝ) (n : ℕ) :
    diff r (fun k => f k - g k) n = diff r f n - diff r g n := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih => simp only [diff_succ, ih]; ring

lemma diff_mul_const (r : ℕ) (f : ℕ → ℝ) (c : ℝ) (n : ℕ) :
    diff r (fun k => f k * c) n = diff r f n * c := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih => simp only [diff_succ, ih]; ring

lemma diff_shift (r : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    diff r (fun k => f (k + 1)) n = diff r f (n + 1) := by
  induction r generalizing n with
  | zero => rfl
  | succ r ih => simp only [diff_succ, ih]

lemma diff_comm (r : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    diff r (fun k => f k - f (k + 1)) n = diff (r + 1) f n := by
  rw [diff_sub, diff_shift, diff_succ]

def CM (f : ℕ → ℝ) : Prop := ∀ r n, 0 ≤ diff r f n

def StrictCM (f : ℕ → ℝ) : Prop := ∀ r n, 0 < diff r f n

lemma StrictCM.cm {f : ℕ → ℝ} (hf : StrictCM f) : CM f :=
  fun r n => (hf r n).le

lemma CM.shift {f : ℕ → ℝ} (hf : CM f) : CM (fun n => f (n + 1)) := by
  intro r n
  rw [diff_shift]
  exact hf r (n + 1)

lemma CM.step {f : ℕ → ℝ} (hf : CM f) : CM (fun n => f n - f (n + 1)) := by
  intro r n
  rw [diff_comm]
  exact hf (r + 1) n

lemma StrictCM.shift {f : ℕ → ℝ} (hf : StrictCM f) :
    StrictCM (fun n => f (n + 1)) := by
  intro r n
  rw [diff_shift]
  exact hf r (n + 1)

lemma StrictCM.step {f : ℕ → ℝ} (hf : StrictCM f) :
    StrictCM (fun n => f n - f (n + 1)) := by
  intro r n
  rw [diff_comm]
  exact hf (r + 1) n

lemma diff_product_rule (r : ℕ) (f g : ℕ → ℝ) (n : ℕ) :
    diff (r + 1) (fun k => f k * g k) n =
      diff r (fun k => (f k - f (k + 1)) * g k) n +
      diff r (fun k => f (k + 1) * (g k - g (k + 1))) n := by
  rw [← diff_add, ← diff_comm]
  congr 2
  funext k
  ring

lemma CM.mul {f g : ℕ → ℝ} (hf : CM f) (hg : CM g) :
    CM (fun n => f n * g n) := by
  intro r
  induction r generalizing f g with
  | zero => intro n; exact mul_nonneg (hf 0 n) (hg 0 n)
  | succ r ih =>
    intro n
    rw [diff_product_rule]
    exact add_nonneg (ih hf.step hg n) (ih hf.shift hg.step n)

lemma StrictCM.mul {f g : ℕ → ℝ} (hf : StrictCM f) (hg : StrictCM g) :
    StrictCM (fun n => f n * g n) := by
  intro r
  induction r generalizing f g with
  | zero => intro n; exact mul_pos (hf 0 n) (hg 0 n)
  | succ r ih =>
    intro n
    rw [diff_product_rule]
    exact add_pos (ih hf.step hg n) (ih hf.shift hg.step n)

lemma StrictCM.mul_const {f : ℕ → ℝ} (hf : StrictCM f) {c : ℝ} (hc : 0 < c) :
    StrictCM (fun n => f n * c) := by
  intro r n
  rw [diff_mul_const]
  exact mul_pos (hf r n) hc

lemma StrictCM.pow_succ {f : ℕ → ℝ} (hf : StrictCM f) (j : ℕ) :
    StrictCM (fun n => f n ^ (j + 1)) := by
  induction j with
  | zero => simpa using hf
  | succ j ih => simpa only [pow_succ] using ih.mul hf

noncomputable def kernel (k n : ℕ) : ℝ :=
  (k.factorial : ℝ) * n.factorial / (n + k + 1).factorial

lemma kernel_pos (k n : ℕ) : 0 < kernel k n := by
  unfold kernel
  positivity

lemma kernel_sub (k n : ℕ) : kernel k n - kernel k (n + 1) = kernel (k + 1) n := by
  unfold kernel
  rw [show n + 1 + k + 1 = (n + k + 1) + 1 by omega,
    show n + (k + 1) + 1 = (n + k + 1) + 1 by omega]
  rw [Nat.factorial_succ (n + k + 1), Nat.factorial_succ n, Nat.factorial_succ k]
  push_cast
  have hF : ((n + k + 1).factorial : ℝ) ≠ 0 := by positivity
  have hN : (n : ℝ) + k + 1 + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma diff_kernel (r k n : ℕ) : diff r (kernel k) n = kernel (k + r) n := by
  induction r generalizing n with
  | zero => simp
  | succ r ih =>
    simp only [diff_succ, ih]
    rw [kernel_sub]
    congr 1

lemma kernel_strictCM (k : ℕ) : StrictCM (kernel k) := by
  intro r n
  rw [diff_kernel]
  exact kernel_pos _ _

lemma ratio_strictCM (k : ℕ) :
    StrictCM (fun n => (n.factorial : ℝ) / (n + k + 1).factorial) := by
  have h := (kernel_strictCM k).mul_const
    (show 0 < (1 : ℝ) / k.factorial by positivity)
  convert h using 1
  funext n
  unfold kernel
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Newton's finite telescoping identity, without assuming convergence. -/
lemma newton_sum (f : ℕ → ℝ) (N n : ℕ) :
    (∑ k ∈ Finset.range (N + 1), diff k f (n + 1)) + diff (N + 1) f n = f n := by
  induction N with
  | zero => simp [diff]
  | succ N ih =>
    rw [Finset.sum_range_succ, diff_succ (N + 1)]
    linarith

lemma CM.order_antitone {f : ℕ → ℝ} (hf : CM f) (n : ℕ) :
    Antitone (fun r => diff r f n) := by
  apply antitone_nat_of_succ_le
  intro r
  simp only [diff_succ]
  linarith [hf r (n + 1)]

/-- One positive shift supplies a bound uniform in the order of the difference. -/
theorem CM.diff_bound {f : ℕ → ℝ} (hf : CM f) (N n : ℕ) :
    diff N f (n + 1) ≤ f n / (N + 1 : ℝ) := by
  have hp : (0 : ℝ) < N + 1 := by positivity
  apply (le_div_iff₀ hp).mpr
  have hsum : (N + 1 : ℝ) * diff N f (n + 1) ≤
      ∑ k ∈ Finset.range (N + 1), diff k f (n + 1) := by
    calc
      _ = ∑ _k ∈ Finset.range (N + 1), diff N f (n + 1) := by simp
      _ ≤ _ := Finset.sum_le_sum fun k hk =>
        hf.order_antitone (n + 1) (by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
  have hnew := newton_sum f N n
  have hpos := hf (N + 1) n
  nlinarith

noncomputable def row (r k n : ℕ) : ℝ :=
  ((n.factorial : ℝ) / (n + k + 1).factorial) ^ (r + 1)

lemma row_strictCM (r k : ℕ) : StrictCM (row r k) :=
  (ratio_strictCM k).pow_succ r

lemma summable_row (r n : ℕ) : Summable (fun k => row r k n) := by
  have hs : Summable (fun k : ℕ => 1 / ((k + 1).factorial : ℝ) ^ (r + 1)) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Erdos68Development.powerTerm, Nat.add_assoc] using
      Erdos68Development.summable_powerTerm r
  have ht := ((summable_nat_add_iff n).mpr hs).mul_left
    ((n.factorial : ℝ) ^ (r + 1))
  convert ht using 1
  funext k
  simp only [row, div_pow, mul_one_div]
  rw [Nat.add_comm n k]

lemma summable_diff_row (r N n : ℕ) : Summable (fun k => diff N (row r k) n) := by
  induction N generalizing n with
  | zero => exact summable_row r n
  | succ N ih => exact (ih n).sub (ih (n + 1))

noncomputable def tail (r n : ℕ) : ℝ := ∑' k, row r k n

lemma diff_tail (r N n : ℕ) :
    diff N (tail r) n = ∑' k, diff N (row r k) n := by
  induction N generalizing n with
  | zero => rfl
  | succ N ih =>
    simp only [diff_succ, ih]
    exact ((summable_diff_row r N n).tsum_sub (summable_diff_row r N (n + 1))).symm

/-- All differences of every scaled factorial-power tail are strictly positive. -/
theorem tail_strictCM (r : ℕ) : StrictCM (tail r) := by
  intro N n
  rw [diff_tail]
  exact (summable_diff_row r N n).tsum_pos
    (fun k => (row_strictCM r k N n).le) 0 (row_strictCM r 0 N n)

/-- A uniform-in-order smallness bound for the positive residuals. -/
theorem tail_diff_bounds (r N n : ℕ) :
    0 < diff N (tail r) (n + 1) ∧
      diff N (tail r) (n + 1) ≤ tail r n / (N + 1 : ℝ) :=
  ⟨tail_strictCM r N (n + 1), (tail_strictCM r).cm.diff_bound N n⟩

open Filter Topology

lemma CM.tendsto_differences {f : ℕ → ℝ} (hf : CM f) (n : ℕ) :
    Tendsto (fun N => diff N f (n + 1)) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => f n / (N + 1 : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_one_div, mul_zero] using h.const_mul (f n)
  exact squeeze_zero (fun N => hf N (n + 1)) (fun N => hf.diff_bound N n) ht

theorem tendsto_tail_differences (r n : ℕ) :
    Tendsto (fun N => diff N (tail r) (n + 1)) atTop (𝓝 0) :=
  (tail_strictCM r).cm.tendsto_differences n

open Erdos68Development

noncomputable def column (r : ℕ) : ℝ := ∑' k, powerTerm r k

def baseA (r n : ℕ) : ℤ := (n + 1).factorial ^ (r + 1)

def baseB (r n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n,
    ((n + 1).factorial ^ (r + 1) / (k + 2).factorial ^ (r + 1) : ℕ)

lemma baseB_cast (r n : ℕ) : (baseB r n : ℝ) =
    ((n + 1).factorial : ℝ) ^ (r + 1) * ∑ k ∈ Finset.range n, powerTerm r k := by
  unfold baseB
  simp only [Int.cast_sum, Int.cast_natCast]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k + 2 ≤ n + 1 := by have := Finset.mem_range.mp hk; omega
  rw [Nat.cast_div_charZero
    (pow_dvd_pow_of_dvd (Nat.factorial_dvd_factorial hk') (r + 1))]
  simp [powerTerm, div_eq_mul_inv]

lemma tail_shift_column (r n : ℕ) :
    tail r (n + 1) = (baseA r n : ℝ) * column r - (baseB r n : ℝ) := by
  have he : tail r (n + 1) = ((n + 1).factorial : ℝ) ^ (r + 1) *
      ∑' k, powerTerm r (k + n) := by
    rw [tail, ← tsum_mul_left]
    apply tsum_congr
    intro k
    simp only [row, powerTerm, div_pow, mul_one_div]
    rw [show n + 1 + k + 1 = k + n + 2 by omega]
  have hs := (summable_powerTerm r).sum_add_tsum_nat_add n
  rw [he, baseB_cast]
  simp only [baseA, Int.cast_pow, Int.cast_natCast]
  unfold column
  rw [← hs]
  ring

lemma tail_zero (r : ℕ) : tail r 0 = 1 + column r := by
  have h := (summable_row r 0).sum_add_tsum_nat_add 1
  have h0 : row r 0 0 = 1 := by simp [row]
  have ht : (∑' k, row r (k + 1) 0) = column r := by
    unfold column
    apply tsum_congr
    intro k
    simp [row, powerTerm]
  simpa only [Finset.sum_range_one, h0, ht, tail] using h.symm

lemma column_lt_one (r : ℕ) : column r < 1 := by
  simpa [column] using (scaled_powerTerm_error r 0).2


def intDiff : ℕ → (ℕ → ℤ) → ℕ → ℤ
  | 0, f, n => f n
  | N + 1, f, n => intDiff N f n - intDiff N f (n + 1)

lemma intDiff_cast (N : ℕ) (f : ℕ → ℤ) (n : ℕ) :
    (intDiff N f n : ℝ) = diff N (fun k => (f k : ℝ)) n := by
  induction N generalizing n with
  | zero => rfl
  | succ N ih => simp only [intDiff, Int.cast_sub, diff_succ, ih]

def coeffA (r N : ℕ) : ℤ := intDiff N (baseA r) 0

def coeffB (r N : ℕ) : ℤ := intDiff N (baseB r) 0

/-- Integer forms, with the sign absorbed into both coefficients. -/
theorem column_form_identity (r N : ℕ) :
    (coeffA r N : ℝ) * column r - coeffB r N = diff N (tail r) 1 := by
  rw [coeffA, coeffB, intDiff_cast, intDiff_cast, ← diff_mul_const, ← diff_sub,
    ← diff_shift]
  congr 2
  funext n
  exact (tail_shift_column r n).symm

theorem column_form_pos (r N : ℕ) :
    0 < (coeffA r N : ℝ) * column r - coeffB r N := by
  rw [column_form_identity]
  exact tail_strictCM r N 1

theorem column_form_upper (r N : ℕ) :
    (coeffA r N : ℝ) * column r - coeffB r N ≤ tail r 0 / (N + 1 : ℝ) := by
  rw [column_form_identity]
  exact (tail_diff_bounds r N 0).2

/-- The same order bound works for every factorial-power column. -/
theorem column_form_uniform_bound (r N : ℕ) :
    0 < (coeffA r N : ℝ) * column r - coeffB r N ∧
      (coeffA r N : ℝ) * column r - coeffB r N < 2 / (N + 1 : ℝ) := by
  refine ⟨column_form_pos r N, (column_form_upper r N).trans_lt ?_⟩
  apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < N + 1)).mpr
  rw [tail_zero]
  linarith [column_lt_one r]


theorem tendsto_column_forms (r : ℕ) :
    Tendsto (fun N => (coeffA r N : ℝ) * column r - coeffB r N) atTop (𝓝 0) := by
  simp_rw [column_form_identity]
  exact tendsto_tail_differences r 0

end CompletelyMonotoneDifferences

#print axioms CompletelyMonotoneDifferences.tail_strictCM
#print axioms CompletelyMonotoneDifferences.column_form_identity
#print axioms CompletelyMonotoneDifferences.column_form_pos
#print axioms CompletelyMonotoneDifferences.tendsto_column_forms

#print axioms CompletelyMonotoneDifferences.column_form_uniform_bound
