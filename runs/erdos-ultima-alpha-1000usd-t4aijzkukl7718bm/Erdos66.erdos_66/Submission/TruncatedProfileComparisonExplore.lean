import Submission.ShortSupportSwapTailExplore
import Submission.BoundaryPairMeanExplore

/-! Weighted interval comparisons for an exact-bracket host. These estimates
keep the endpoints of truncated reflection intervals intact. -/
namespace Erdos66TruncatedProfileComparison
open Erdos66ClampedPrefixContinuation Erdos66Generating Erdos66Counting
  Erdos66Fractional Erdos66Rounding Erdos66ShortSupportSwapTail
  Erdos66ReflectionRoundingPatch Erdos66BracketOrderedExchange
open scoped Classical
set_option maxHeartbeats 2600000

lemma weighted_prefix_identity (e w : ℕ → ℝ) (m : ℕ) :
    (∑ i∈Finset.range m, e i*w i)=mass e m*w m+
      ∑ i∈Finset.range m, mass e (i+1)*(w i-w (i+1)) := by
  induction m with
  | zero => simp [mass]
  | succ m ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ,ih,mass_succ]
    ring

lemma weighted_prefix_bound (e w : ℕ → ℝ) (m : ℕ) (D : ℝ)
    (he : ∀ k ≤ m, |mass e k| ≤ D) :
    |∑ i∈Finset.range m, e i*w i| ≤
      D*(|w m|+∑ i∈Finset.range m, |w i-w (i+1)|) := by
  rw [weighted_prefix_identity]
  calc
    _ ≤ |mass e m*w m|+∑ i∈Finset.range m, |mass e (i+1)*(w i-w (i+1))| :=
      (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ D*|w m|+∑ i∈Finset.range m, D*|w i-w (i+1)| := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (he m le_rfl) (abs_nonneg _)
      · apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (he (i+1) (by have := Finset.mem_range.mp hi; omega)) (abs_nonneg _)
    _ = _ := by rw [←Finset.mul_sum,mul_add]

lemma monotone_weighted_prefix_bound (e w : ℕ → ℝ) (m : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (he : ∀ k ≤ m, |mass e k| ≤ D)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (hmono : Monotone w ∨ Antitone w) :
    |∑ i∈Finset.range m, e i*w i| ≤ 2*D := by
  have hh := weighted_prefix_bound e w m D he
  have hvar : (∑ i∈Finset.range m, |w i-w (i+1)|) ≤ 1 := by
    rcases hmono with hm | hm
    · simp_rw [abs_of_nonpos (sub_nonpos.mpr (hm (Nat.le_succ _))),neg_sub]
      have ht : (∑ i∈Finset.range m, (w (i+1)-w i))=w m-w 0 := by
        clear he hh
        induction m with
        | zero => simp
        | succ m ih => rw [Finset.sum_range_succ,ih]; ring
      rw [ht]
      linarith [(hw m).2,(hw 0).1]
    · simp_rw [abs_of_nonneg (sub_nonneg.mpr (hm (Nat.le_succ _)))]
      have ht : (∑ i∈Finset.range m, (w i-w (i+1)))=w 0-w m := by
        clear he hh
        induction m with
        | zero => simp
        | succ m ih => rw [Finset.sum_range_succ,ih]; ring
      rw [ht]
      linarith [(hw 0).2,(hw m).1]
  rw [abs_of_nonneg (hw m).1] at hh
  have hb : w m+(∑ i∈Finset.range m, |w i-w (i+1)|) ≤ 2 := by linarith [(hw m).2]
  exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left hb hD])

lemma shifted_indicator_error (p : ℕ → ℝ) (A : Set ℕ)
    (hbr : ∀ L, PrefixBrackets p A L) (a k : ℕ) :
    |mass (fun i ↦ indicator A (a+i)-p (a+i)) k| ≤ 2 := by
  have hh := local_count_error A p 1 (brackets_count_discrepancy p A hbr) a (a+k) (by omega)
  have hc : ((intervalPart A a (a+k)).card : ℝ)=∑ i∈Finset.Ico a (a+k), indicator A i := by
    simp [intervalPart,indicator]
  rw [hc,←Finset.sum_sub_distrib,Finset.sum_Ico_eq_sum_range] at hh
  simpa only [Nat.add_sub_cancel_left,add_comm,mass,mul_one] using hh

lemma weighted_interval_comparison (p w : ℕ → ℝ) (A : Set ℕ)
    (hbr : ∀ L, PrefixBrackets p A L)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (hmono : Monotone w ∨ Antitone w) (a b : ℕ) :
    |(∑ i∈Finset.Ico a b, indicator A i*w i)-(∑ i∈Finset.Ico a b, p i*w i)| ≤ 4 := by
  rw [←Finset.sum_sub_distrib,Finset.sum_Ico_eq_sum_range]
  simp_rw [←sub_mul]
  have hm : Monotone (fun i ↦ w (a+i)) ∨ Antitone (fun i ↦ w (a+i)) := by
    rcases hmono with h | h
    · exact Or.inl (fun i j hij ↦ h (Nat.add_le_add_left hij a))
    · exact Or.inr (fun i j hij ↦ h (Nat.add_le_add_left hij a))
  convert monotone_weighted_prefix_bound
    (fun i ↦ indicator A (a+i)-p (a+i)) (fun i ↦ w (a+i)) (b-a) 2 (by norm_num)
    (fun k _ ↦ shifted_indicator_error p A hbr a k) (fun i ↦ hw (a+i)) hm using 1; norm_num [add_comm]

lemma truncated_mixed_comparison (A : Set ℕ) (hbr : ∀ L, PrefixBrackets profile A L)
    (n a b : ℕ) :
    |(∑ i∈Finset.Ico a b, indicator A i*profile (n-i))-
      (∑ i∈Finset.Ico a b, profile i*profile (n-i))| ≤ 4 := by
  apply weighted_interval_comparison profile (fun i ↦ profile (n-i)) A hbr
    (fun i ↦ ⟨profile_nonneg _,profile_le_one _⟩)
  exact Or.inl (fun i j hij ↦ profile_antitone (Nat.sub_le_sub_left hij n))

end Erdos66TruncatedProfileComparison
