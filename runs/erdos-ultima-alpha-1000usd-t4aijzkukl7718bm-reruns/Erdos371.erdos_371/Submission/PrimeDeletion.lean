import FormalConjecturesUtil
import Submission.SmallPrimeAveraging

/-! Exact prime-deletion errors for observables of the largest prime factor.
The error is supported on at most one prime. No cancellation of the resulting
affine signed average is asserted. -/

namespace Erdos371PrimeDeletion

open Finset Filter Erdos371SmallPrimeAveraging
open scoped Topology

abbrev P := Nat.maxPrimeFac

lemma quotient_height_le {n p : ℕ} (hp : p.Prime) (hd : p ∣ n) :
    P (n / p) ≤ P n := by
  by_cases hn : n = 0
  · subst n
    simp [P]
  have hq : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) hp.pos).ne'
  have he := Nat.maxPrimeFac_mul hq hp.ne_zero
  rw [Nat.div_mul_cancel hd, hp.maxPrimeFac_eq_self] at he
  change (n / p).maxPrimeFac ≤ n.maxPrimeFac
  rw [he]
  exact le_max_left _ _

lemma quotient_height_eq {n p : ℕ} (hp : p.Prime) (hd : p ∣ n)
    (hne : p ≠ P n) : P (n / p) = P n := by
  by_cases hn : n = 0
  · subst n
    simp [P]
  have hq : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) hp.pos).ne'
  have he := Nat.maxPrimeFac_mul hq hp.ne_zero
  rw [Nat.div_mul_cancel hd, hp.maxPrimeFac_eq_self] at he
  change P n = max (P (n / p)) p at he
  omega

/-- Only deletion of the largest prime can change an observable of it. -/
def error (F : ℕ → ℝ) (p n : ℕ) : ℝ :=
  if p ∣ n then F (P (n / p)) - F (P n) else 0

lemma error_eq_zero {p n : ℕ} (hp : p.Prime) (hne : p ≠ P n) (F : ℕ → ℝ) :
    error F p n = 0 := by
  unfold error
  split_ifs with hd
  · rw [quotient_height_eq hp hd hne, sub_self]
  · rfl

lemma error_sum_eq (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (F : ℕ → ℝ) (n : ℕ) :
    (∑ p ∈ s, error F p n) =
      if P n ∈ s then F (P (n / P n)) - F (P n) else 0 := by
  have he : (∑ p ∈ s, error F p n) =
      ∑ p ∈ s, if p = P n then error F p n else 0 := by
    apply sum_congr rfl
    intro p hp
    by_cases h : p = P n
    · simp [h]
    · simp [h, error_eq_zero (hs p hp) h F]
  rw [he, sum_ite_eq']
  simp [error, Nat.maxPrimeFac_dvd]

lemma abs_error_sum_le_two (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (F : ℕ → ℝ) (hF : ∀ k, |F k| ≤ 1) (n : ℕ) :
    |∑ p ∈ s, error F p n| ≤ 2 := by
  rw [error_sum_eq s hs F n]
  split_ifs
  · exact (abs_sub _ _).trans (by linarith [hF (P (n / P n)), hF (P n)])
  · norm_num

lemma sum_abs_error_le_two (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (F : ℕ → ℝ) (hF : ∀ k, |F k| ≤ 1) (n : ℕ) :
    (∑ p ∈ s, |error F p n|) ≤ 2 := by
  have he : (∑ p ∈ s, |error F p n|) =
      ∑ p ∈ s, if p = P n then |error F p n| else 0 := by
    apply sum_congr rfl
    intro p hp
    by_cases h : p = P n
    · simp [h]
    · simp [h, error_eq_zero (hs p hp) h F]
  rw [he, sum_ite_eq']
  split_ifs
  · simp only [error, Nat.maxPrimeFac_dvd, if_true]
    exact (abs_sub _ _).trans (by linarith [hF (P (n / P n)), hF (P n)])
  · norm_num

def compare (a b : ℕ) : ℝ := if a < b then 1 else -1

def rightDeleted (s : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ s, if p ∣ n + 1 then compare (P n) (P ((n + 1) / p)) else 0

lemma rightDeleted_error_eq (s : Finset ℕ) (n : ℕ) :
    rightDeleted s n - (Erdos371PrimeDiscrepancy.sign n : ℝ) * smallCount s n =
      ∑ p ∈ s, error (compare (P n)) p (n + 1) := by
  simp only [rightDeleted, smallCount, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  simp only [error, ind]
  split_ifs with hd
  · simp [compare, Erdos371PrimeDiscrepancy.sign, P]
  · simp

lemma rightDeleted_error_bounds (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (n : ℕ) :
    -2 ≤ rightDeleted s n - (Erdos371PrimeDiscrepancy.sign n : ℝ) * smallCount s n ∧
    rightDeleted s n - (Erdos371PrimeDiscrepancy.sign n : ℝ) * smallCount s n ≤ 0 := by
  rw [rightDeleted_error_eq]
  constructor
  · have hF (k : ℕ) : |compare (P n) k| ≤ 1 := by
      unfold compare
      split_ifs <;> norm_num
    exact (abs_le.mp (abs_error_sum_le_two s hs _ hF (n + 1))).1
  · apply sum_nonpos
    intro p hp
    unfold error
    split_ifs with hd
    · have hh := quotient_height_le (hs p hp) hd
      unfold compare
      split_ifs <;> norm_num
      omega
    · rfl

lemma rightDeleted_mean_error_bound (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (N : ℕ) :
    |mean (rightDeleted s) N -
      mean (fun n => (Erdos371PrimeDiscrepancy.sign n : ℝ) * smallCount s n) N| ≤ 2 := by
  rw [← mean_sub]
  by_cases hN : N = 0
  · subst N
    simp [mean]
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hb : |∑ n ∈ range N, (rightDeleted s n -
      (Erdos371PrimeDiscrepancy.sign n : ℝ) * smallCount s n)| ≤ (N : ℝ) * 2 := by
    calc
      _ ≤ ∑ n ∈ range N, |rightDeleted s n -
          (Erdos371PrimeDiscrepancy.sign n : ℝ) * smallCount s n| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ range N, (2 : ℝ) := by
        apply sum_le_sum
        intro n _
        have h := rightDeleted_error_bounds s hs n
        exact abs_le.mpr ⟨h.1, h.2.trans (by norm_num)⟩
      _ = _ := by simp
  simp only [mean, abs_div, abs_of_pos hn]
  exact (div_le_iff₀ hn).mpr (by simpa only [mul_comm] using hb)

/-- Uniform in the finite prime set, including sets which grow with `N`.
The variance and the affine average on the right still require estimates. -/
lemma signed_mean_approximation (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (N : ℕ) :
    |mass s * (Erdos371PrimeDiscrepancy.total N : ℝ) / N - mean (rightDeleted s) N| ≤
      Real.sqrt (varianceMean s N) + 2 := by
  let W := mean (fun n => (Erdos371PrimeDiscrepancy.sign n : ℝ) * smallCount s n) N
  have hv : |mass s * (Erdos371PrimeDiscrepancy.total N : ℝ) / N - W| ≤
      Real.sqrt (varianceMean s N) := by
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs]
    exact signed_averaging_square_bound s N
  have he : |W - mean (rightDeleted s) N| ≤ 2 := by
    rw [abs_sub_comm]
    exact rightDeleted_mean_error_bound s hs N
  calc
    _ = |(mass s * (Erdos371PrimeDiscrepancy.total N : ℝ) / N - W) +
        (W - mean (rightDeleted s) N)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hv he)

lemma prime_affine_reindex {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∑ n ∈ range N, if p ∣ n + 1 then compare (P n) (P ((n + 1) / p)) else 0) =
      ∑ a ∈ Icc 1 (N / p), compare (P (a * p - 1)) (P a) := by
  rw [← sum_filter]
  apply sum_bij (fun n _ => (n + 1) / p)
  · intro n hn
    obtain ⟨hnN, hd⟩ := mem_filter.mp hn
    have hnlt := mem_range.mp hnN
    refine mem_Icc.mpr ⟨?_, Nat.div_le_div_right (by omega : n + 1 ≤ N)⟩
    exact Nat.div_pos (Nat.le_of_dvd (by omega : 0 < n + 1) hd) hp
  · intro n hn m hm he
    have hnfac := Nat.div_mul_cancel (mem_filter.mp hn).2
    have hmfac := Nat.div_mul_cancel (mem_filter.mp hm).2
    change (n + 1) / p = (m + 1) / p at he
    rw [he] at hnfac
    omega
  · intro a ha
    obtain ⟨ha1, haN⟩ := mem_Icc.mp ha
    have hap : 0 < a * p := Nat.mul_pos (by omega) hp
    have hapN := (Nat.le_div_iff_mul_le hp).mp haN
    have he : a * p - 1 + 1 = a * p := by omega
    refine ⟨a * p - 1, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, ?_⟩
    · rw [he]
      exact dvd_mul_left p a
    · rw [he, Nat.mul_div_cancel _ hp]
  · intro n hn
    have he := Nat.div_mul_cancel (mem_filter.mp hn).2
    rw [he, Nat.add_sub_cancel]

lemma rightDeleted_sum_eq_affine (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (N : ℕ) :
    (∑ n ∈ range N, rightDeleted s n) =
      ∑ p ∈ s, ∑ a ∈ Icc 1 (N / p), compare (P (a * p - 1)) (P a) := by
  unfold rightDeleted
  rw [sum_comm]
  exact sum_congr rfl (fun p hp => prime_affine_reindex (hs p hp).pos N)

end Erdos371PrimeDeletion

#print axioms Erdos371PrimeDeletion.quotient_height_eq
#print axioms Erdos371PrimeDeletion.sum_abs_error_le_two
#print axioms Erdos371PrimeDeletion.rightDeleted_error_bounds
#print axioms Erdos371PrimeDeletion.signed_mean_approximation
#print axioms Erdos371PrimeDeletion.rightDeleted_sum_eq_affine
