import Submission.RawMomentExplore
import Submission.WeightedLogExplore

/-!
# A strict obstruction to a flat cyclic-prefix model

A logarithmic witness cannot have A(N)^2/(N log N) tending to the same constant c.
This is a necessary condition, not a proof or disproof of Erdős Problem 66.
-/

namespace Erdos66PrefixMoment
open Filter AdditiveCombinatorics Erdos66Counting Erdos66Cumulative
  Erdos66WeightedLog Erdos66RawMoment
open scoped Topology

lemma weighted_tail_bound {X : Type*} (S : Finset X) (P : X → Prop) [DecidablePred P]
    (w : X → ℝ) (C : ℝ) (hw : ∀ x ∈ S, 0 ≤ w x ∧ w x ≤ C) :
    0 ≤ (∑ x ∈ S, w x) - ∑ x ∈ S.filter P, w x ∧
      (∑ x ∈ S, w x) - ∑ x ∈ S.filter P, w x ≤
        C * ((S.card : ℝ) - (S.filter P).card) := by
  classical
  have hs := Finset.sum_filter_add_sum_filter_not S P w
  have hc := Finset.filter_card_add_filter_neg_card_eq_card (s := S) P
  have hc' : ((S.filter P).card : ℝ) + (S.filter (fun x ↦ ¬ P x)).card = S.card := by
    exact_mod_cast hc
  have hlo : 0 ≤ ∑ x ∈ S.filter (fun x ↦ ¬P x), w x :=
    Finset.sum_nonneg (fun x hx ↦ (hw x (Finset.mem_filter.mp hx).1).1)
  have hhi : (∑ x ∈ S.filter (fun x ↦ ¬P x), w x) ≤
      (S.filter (fun x ↦ ¬P x)).card * C := by
    calc
      _ ≤ ∑ _x ∈ S.filter (fun x ↦ ¬P x), C :=
        Finset.sum_le_sum (fun x hx ↦ (hw x (Finset.mem_filter.mp hx).1).2)
      _ = _ := by simp
  have hc'' : ((S.filter (fun x ↦ ¬P x)).card : ℝ) = (S.card : ℝ) - (S.filter P).card := by linarith
  rw [hc''] at hhi
  constructor <;> nlinarith

lemma low_pair_sum (A : Set ℕ) (N : ℕ) (w : ℕ → ℝ) :
    (∑ ab ∈ ((cutoff A N) ×ˢ (cutoff A N)).filter (fun ab ↦ ab.1 + ab.2 < N),
      w (ab.1 + ab.2)) = ∑ n ∈ Finset.range N, w n * (sumRep A n : ℝ) := by
  classical
  have hf := Finset.sum_fiberwise_eq_sum_filter ((cutoff A N) ×ˢ (cutoff A N))
    (Finset.range N) (fun ab : ℕ × ℕ ↦ ab.1 + ab.2) (fun ab ↦ w (ab.1 + ab.2))
  simp only [Finset.mem_range] at hf
  rw [← hf]
  apply Finset.sum_congr rfl
  intro n hn
  rw [sumRep_eq_fiber_card A N n (Finset.mem_range.mp hn)]
  simp only [Finset.product_eq_sprod]
  have hs := Finset.sum_eq_card_nsmul (s := ((cutoff A N) ×ˢ (cutoff A N)).filter
    (fun ab : ℕ × ℕ ↦ ab.1 + ab.2 = n)) (b := w n)
    (fun ab hab ↦ congrArg w (Finset.mem_filter.mp hab).2)
  simpa only [nsmul_eq_mul, mul_comm] using hs

noncomputable def fullMoment (A : Set ℕ) (N k : ℕ) : ℝ :=
  ∑ ab ∈ (cutoff A N) ×ˢ (cutoff A N), (((ab.1 + ab.2 : ℕ) : ℝ) / N) ^ k

noncomputable def lowMoment (A : Set ℕ) (N k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, ((n : ℝ) / N) ^ k * (sumRep A n : ℝ)

lemma moment_tail_bounds (A : Set ℕ) (N k : ℕ) (hN : 0 < N) :
    0 ≤ fullMoment A N k - lowMoment A N k ∧
      fullMoment A N k - lowMoment A N k ≤ (2 : ℝ) ^ k *
        ((count A N : ℝ) ^ 2 - ∑ n ∈ Finset.range N, (sumRep A n : ℝ)) := by
  classical
  have hb := weighted_tail_bound ((cutoff A N) ×ˢ (cutoff A N))
    (fun ab : ℕ × ℕ ↦ ab.1 + ab.2 < N)
    (fun ab : ℕ × ℕ ↦ (((ab.1 + ab.2 : ℕ) : ℝ) / N) ^ k) ((2 : ℝ) ^ k) (by
      intro ab hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      have ha' := (mem_cutoff.mp ha).1
      have hb' := (mem_cutoff.mp hb).1
      constructor
      · positivity
      · apply pow_le_pow_left₀ (by positivity)
        apply (div_le_iff₀ (by exact_mod_cast hN)).mpr
        exact_mod_cast (show ab.1 + ab.2 ≤ 2 * N by omega))
  rw [low_pair_sum A N (fun n ↦ ((n : ℝ) / N) ^ k)] at hb
  have hc := low_pair_sum A N (fun _ ↦ (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at hc
  rw [hc] at hb
  simpa only [fullMoment, lowMoment, Finset.card_product, Nat.cast_mul, count, pow_two] using hb

lemma full_moment_limit_of_count_limit {A : Set ℕ} {c : ℝ}
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c))
    (hcount : Tendsto (fun n ↦ (count A n : ℝ) ^ 2 / ((n : ℝ) * Real.log n)) atTop (𝓝 c))
    (k : ℕ) (hk : k ≤ 4) :
    Tendsto (fun n : ℕ ↦ fullMoment A n k / ((n : ℝ) * Real.log n))
      atTop (𝓝 (c / ((k : ℝ) + 1))) := by
  have hlow := log_weighted_power_limit h k hk
  have htail := (hcount.sub (cumulative_sumRep_limit h)).const_mul ((2 : ℝ) ^ k)
  simp only [sub_self, mul_zero] at htail
  have herr : Tendsto (fun n : ℕ ↦ (fullMoment A n k - lowMoment A n k) /
      ((n : ℝ) * Real.log n)) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ htail
    · filter_upwards [eventually_ge_atTop 2] with n hn
      exact div_nonneg (moment_tail_bounds A n k (by omega)).1
        (mul_nonneg (Nat.cast_nonneg _) (log_nat_nonneg _))
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hb := (moment_tail_bounds A n k (by omega)).2
      have hh := div_le_div_of_nonneg_right hb
        (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (log_nat_nonneg n))
      simpa only [mul_div_assoc, sub_div] using hh
  have hh := hlow.add herr
  simp only [add_zero] at hh
  apply hh.congr'
  filter_upwards [] with n
  dsimp only [lowMoment]
  ring

lemma pairMoment_cutoff_eq (A : Set ℕ) (N k : ℕ) :
    pairMoment (cutoff A N) (fun a : ℕ ↦ (a : ℝ) / N) k =
      fullMoment A N k / (count A N : ℝ) ^ 2 := by
  simp only [pairMoment, avg, fullMoment, count, Nat.cast_add, add_div,
    Finset.card_product, Nat.cast_mul, pow_two]

lemma pair_moment_limit_of_count_limit {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c))
    (hcount : Tendsto (fun n ↦ (count A n : ℝ) ^ 2 / ((n : ℝ) * Real.log n)) atTop (𝓝 c))
    (k : ℕ) (hk : k ≤ 4) :
    Tendsto (fun n : ℕ ↦ pairMoment (cutoff A n) (fun a : ℕ ↦ (a : ℝ) / n) k)
      atTop (𝓝 (1 / ((k : ℝ) + 1))) := by
  have hh := (full_moment_limit_of_count_limit h hcount k hk).div hcount hc
  have hlim : Tendsto (fun n : ℕ ↦
      (fullMoment A n k / ((n : ℝ) * Real.log n)) /
        ((count A n : ℝ) ^ 2 / ((n : ℝ) * Real.log n)))
      atTop (𝓝 (1 / ((k : ℝ) + 1))) := by
    convert hh using 1
    field_simp
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hl0 : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  rw [pairMoment_cutoff_eq]
  exact div_div_div_cancel_right₀ (mul_ne_zero hn0 hl0) _ _

/-- The lower constant in the elementary counting bounds cannot be the actual limit.
This is not a negation of the Erdős conjecture: its expected counting constant is larger. -/
lemma count_limit_ne_coefficient {A : Set ℕ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun n ↦ (sumRep A n : ℝ) / Real.log n) atTop (𝓝 c)) :
    ¬ Tendsto (fun n ↦ (count A n : ℝ) ^ 2 / ((n : ℝ) * Real.log n)) atTop (𝓝 c) := by
  intro hcount
  apply not_uniform_moment_limits_any (cutoff A) (fun n a ↦ (a : ℝ) / n)
  · convert pair_moment_limit_of_count_limit hc h hcount 1 (by norm_num) using 1 <;> norm_num
  · convert pair_moment_limit_of_count_limit hc h hcount 2 (by norm_num) using 1 <;> norm_num
  · convert pair_moment_limit_of_count_limit hc h hcount 3 (by norm_num) using 1 <;> norm_num
  · convert pair_moment_limit_of_count_limit hc h hcount 4 (by norm_num) using 1 <;> norm_num

end Erdos66PrefixMoment
