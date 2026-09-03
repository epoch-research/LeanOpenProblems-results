import FormalConjecturesUtil
import Submission.RestrictedCRTDiscrepancy

/-! Exact reflected-root formulas for the two CRT progression counts.
The one-pair discrepancy is bounded by one but need not change sign as
its cutoff varies. No cancellation over prime pairs is deduced. -/

namespace Erdos371CRTReflectedRoot

open Finset Erdos371CofactorSieve
open Erdos371SubcriticalPrimePairCancellation (count)

lemma initial_count {a b r L : ℕ} (hab : a.Coprime b) (hr : r<a*b)
    (har : a ∣ r) (hbr : b ∣ r+1) (hL : L ≤ a*b) :
    count a b L = if r<L then 1 else 0 := by
  have he : (range L).filter (fun n => a ∣ n ∧ b ∣ n+1) =
      if r<L then {r} else ∅ := by
    ext n
    have huniq (hn : n<L) (han : a ∣ n) (hbn : b ∣ n+1) : n=r := by
      have hh := progression_remainder hab hr har hbr han hbn
      simpa [Nat.mod_eq_of_lt (hn.trans_le hL)] using hh
    by_cases hrL : r<L
    · simp only [if_pos hrL,mem_filter,mem_range,mem_singleton]
      exact ⟨fun hn => huniq hn.1 hn.2.1 hn.2.2,fun h => h ▸ ⟨hrL,har,hbr⟩⟩
    · simp only [if_neg hrL,Finset.notMem_empty,mem_filter,mem_range,iff_false,not_and]
      intro hn han hbn
      exact hrL ((huniq hn han hbn) ▸ hn)
  unfold count
  rw [he]
  split_ifs <;> simp

lemma count_eq_div_add_indicator {a b r : ℕ} (ha : 0<a) (hb : 0<b)
    (hab : a.Coprime b) (hr : r<a*b) (har : a ∣ r) (hbr : b ∣ r+1) (N : ℕ) :
    count a b N = N/(a*b) + if r<N%(a*b) then 1 else 0 := by
  have hper (n : ℕ) : (a ∣ n+a*b ∧ b ∣ n+a*b+1) ↔ (a ∣ n ∧ b ∣ n+1) := by
    have he : n+a*b+1=(n+1)+a*b := by omega
    rw [he,← Nat.dvd_add_iff_left (dvd_mul_right a b),
      ← Nat.dvd_add_iff_left (dvd_mul_left b a)]
  have hh := Erdos371Exploration.periodic_count_remainder
    (fun n => a ∣ n ∧ b ∣ n+1) hper N
  change count a b N = N/(a*b)*count a b (a*b) + count a b (N%(a*b)) at hh
  rw [initial_count hab hr har hbr le_rfl,if_pos hr,mul_one,
    initial_count hab hr har hbr (Nat.mod_lt N (Nat.mul_pos ha hb)).le] at hh
  exact hh

lemma reflected_root {a b r : ℕ} (hr : r<a*b) (har : a ∣ r) (hbr : b ∣ r+1) :
    a*b-1-r < b*a ∧ b ∣ a*b-1-r ∧ a ∣ (a*b-1-r)+1 := by
  have he : a*b-1-r=a*b-(r+1) := by omega
  have he' : (a*b-1-r)+1=a*b-r := by omega
  refine ⟨by rw [Nat.mul_comm b a]; omega,?_,?_⟩
  · rw [he]
    exact Nat.dvd_sub (dvd_mul_left b a) hbr
  · rw [he']
    exact Nat.dvd_sub (dvd_mul_right a b) har

/-- Both full-period counts cancel; only the two reflected roots remain. -/
theorem difference_eq_indicators {a b r : ℕ} (ha : 0<a) (hb : 0<b)
    (hab : a.Coprime b) (hr : r<a*b) (har : a ∣ r) (hbr : b ∣ r+1) (N : ℕ) :
    (count a b N : ℝ)-count b a N =
      (if r<N%(a*b) then 1 else 0) - (if a*b-1-r<N%(a*b) then 1 else 0) := by
  have ht := reflected_root hr har hbr
  rw [count_eq_div_add_indicator ha hb hab hr har hbr,
    count_eq_div_add_indicator hb ha hab.symm ht.1 ht.2.1 ht.2.2]
  simp only [Nat.mul_comm b a,Nat.cast_add,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  ring

/-- A sharp version of the single-pair progression discrepancy bound. -/
theorem difference_abs_le_one {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (hab : a.Coprime b) (N : ℕ) :
    |(count a b N : ℝ)-count b a N| ≤ 1 := by
  obtain ⟨r,hr,har,hbr⟩ := exists_progression_origin ha hb hab
  rw [difference_eq_indicators ha hb hab hr har hbr]
  split_ifs <;> norm_num

/-- When the first root is earlier, its count is never smaller, at any cutoff. -/
theorem difference_nonneg_of_root_order {a b r : ℕ} (ha : 0<a) (hb : 0<b)
    (hab : a.Coprime b) (hr : r<a*b) (har : a ∣ r) (hbr : b ∣ r+1)
    (horder : r ≤ a*b-1-r) (N : ℕ) :
    0 ≤ (count a b N : ℝ)-count b a N := by
  rw [difference_eq_indicators ha hb hab hr har hbr]
  split_ifs <;> norm_num <;> omega

/-- The opposite ordering gives the opposite inequality for every cutoff. -/
theorem difference_nonpos_of_root_order {a b r : ℕ} (ha : 0<a) (hb : 0<b)
    (hab : a.Coprime b) (hr : r<a*b) (har : a ∣ r) (hbr : b ∣ r+1)
    (horder : a*b-1-r ≤ r) (N : ℕ) :
    (count a b N : ℝ)-count b a N ≤ 0 := by
  rw [difference_eq_indicators ha hb hab hr har hbr]
  split_ifs <;> norm_num <;> omega

lemma sum_cutoff_indicator {r M : ℕ} (hr : r<M) :
    (∑ N ∈ range M, if r<N then (1 : ℝ) else 0) = (M : ℝ)-r-1 := by
  rw [sum_boole]
  have he : (range M).filter (fun N => r<N) = Ioo r M := by
    ext N
    simp only [mem_filter,mem_range,mem_Ioo]
    omega
  rw [he,Nat.card_Ioo]
  have he' : M-r-1=M-(r+1) := by omega
  rw [he',Nat.cast_sub (by omega : r+1 ≤ M),Nat.cast_add,Nat.cast_one]
  ring

/-- Averaging the cutoff across one full period need not cancel the pair
bias. It gives the distance between its reflected roots, with sign. -/
theorem sum_difference_over_period {a b r : ℕ} (hab : a.Coprime b)
    (hr : r<a*b) (har : a ∣ r) (hbr : b ∣ r+1) :
    (∑ N ∈ range (a*b), ((count a b N : ℝ)-count b a N)) =
      (a*b-1-r : ℕ) - (r : ℝ) := by
  have ht := reflected_root hr har hbr
  have he (N : ℕ) (hN : N ∈ range (a*b)) :
      (count a b N : ℝ)-count b a N =
        (if r<N then 1 else 0) - (if a*b-1-r<N then 1 else 0) := by
    rw [initial_count hab hr har hbr (mem_range.mp hN).le,
      initial_count hab.symm ht.1 ht.2.1 ht.2.2 (by have := mem_range.mp hN; nlinarith)]
    simp only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [sum_congr rfl he,sum_sub_distrib,sum_cutoff_indicator hr,
    sum_cutoff_indicator (by simpa [Nat.mul_comm] using ht.1)]
  ring

lemma nonzero_period_average_example :
    (∑ N ∈ range 10, ((count 2 5 N : ℝ)-count 5 2 N)) = 1 := by
  have hh := sum_difference_over_period (a := 2) (b := 5) (r := 4)
    (by decide) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hh
  simpa only [sum_sub_distrib] using hh


end Erdos371CRTReflectedRoot

#print axioms Erdos371CRTReflectedRoot.difference_eq_indicators
#print axioms Erdos371CRTReflectedRoot.difference_abs_le_one
#print axioms Erdos371CRTReflectedRoot.difference_nonneg_of_root_order

#print axioms Erdos371CRTReflectedRoot.sum_difference_over_period
#print axioms Erdos371CRTReflectedRoot.nonzero_period_average_example
