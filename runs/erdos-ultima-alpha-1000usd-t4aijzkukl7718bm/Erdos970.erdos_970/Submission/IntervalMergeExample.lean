import Submission.IntervalTwoSidedWord
import Submission.IntervalHullWheelThirty

/-! Two compatible integral pairs can have an incompatible pointwise merge,
even when a common binary word satisfies both. This example is not a prime-order
recurrence computation and does not give a Jacobsthal estimate. -/
namespace Erdos970.IntervalRescaling.IntegerHull.MergeExample
open WheelThirty

/-- Exact circular count tables of 100100111100 and 111000111000. The proofs
below verify their shape directly; no unproved profile characterization is used. -/
def loTable (i : Fin 2) : List ℤ :=
  if i = 0 then [0,0,0,1,1,1,2,2,2,3,4,5] else [0,0,0,0,1,2,3,3,3,3,4,5]

def hiTable (i : Fin 2) : List ℤ :=
  if i = 0 then [0,1,2,3,4,4,4,5,5,5,6,6] else [0,1,2,3,3,3,3,4,5,6,6,6]

def lower (i : Fin 2) : ℕ → ℤ := extend 12 6 (fun n => (loTable i)[n]!)
def upper (i : Fin 2) : ℕ → ℤ := extend 12 6 (fun n => (hiTable i)[n]!)

private lemma finite_shape : ∀ i : Fin 2, ∀ m n : Fin 12,
    lower i n ≤ lower i (m.val + n.val) - lower i m ∧
    lower i (m.val + n.val) - lower i m ≤ upper i n ∧
    lower i n ≤ upper i (m.val + n.val) - upper i m ∧
    upper i (m.val + n.val) - upper i m ≤ upper i n := by decide +kernel

private lemma tables_nonneg : ∀ (i : Fin 2) (n : Fin 12),
    0 ≤ (loTable i)[n.val]! ∧ 0 ≤ (hiTable i)[n.val]! := by decide +kernel

lemma nonneg (i : Fin 2) (n : ℕ) : 0 ≤ lower i n ∧ 0 ≤ upper i n := by
  have hh := tables_nonneg i ⟨n % 12, Nat.mod_lt _ (by omega)⟩
  constructor
  · exact add_nonneg (by positivity) hh.1
  · exact add_nonneg (by positivity) hh.2

lemma compatible (i : Fin 2) :
    Compatible (fun n => (lower i n : ℝ)) (fun n => (upper i n : ℝ)) := by
  have hshape (m n : ℕ) :
      lower i n ≤ lower i (m+n)-lower i m ∧ lower i (m+n)-lower i m ≤ upper i n ∧
      lower i n ≤ upper i (m+n)-upper i m ∧ upper i (m+n)-upper i m ≤ upper i n := by
    have hh := finite_shape i ⟨m % 12, Nat.mod_lt _ (by omega)⟩
      ⟨n % 12, Nat.mod_lt _ (by omega)⟩
    have hll := extend_defect 12 (by omega) 6 (fun n => (loTable i)[n]!)
      (fun n => (loTable i)[n]!) m n
    have hlu := extend_defect 12 (by omega) 6 (fun n => (loTable i)[n]!)
      (fun n => (hiTable i)[n]!) m n
    have hul := extend_defect 12 (by omega) 6 (fun n => (hiTable i)[n]!)
      (fun n => (loTable i)[n]!) m n
    have huu := extend_defect 12 (by omega) 6 (fun n => (hiTable i)[n]!)
      (fun n => (hiTable i)[n]!) m n
    change lower i (m+n)-lower i m-lower i n =
      lower i (m%12+n%12)-lower i (m%12)-lower i (n%12) at hll
    change lower i (m+n)-lower i m-upper i n =
      lower i (m%12+n%12)-lower i (m%12)-upper i (n%12) at hlu
    change upper i (m+n)-upper i m-lower i n =
      upper i (m%12+n%12)-upper i (m%12)-lower i (n%12) at hul
    change upper i (m+n)-upper i m-upper i n =
      upper i (m%12+n%12)-upper i (m%12)-upper i (n%12) at huu
    dsimp only at hh
    omega
  refine ⟨?_, ?_, fun n => by exact_mod_cast (nonneg i n).2, ?_, ?_⟩
  · fin_cases i <;> norm_num [lower, extend, loTable]
  · fin_cases i <;> norm_num [upper, extend, hiTable]
  · intro m n
    constructor
    · exact_mod_cast (hshape m n).1
    · exact_mod_cast (hshape m n).2.1
  · intro m n
    exact_mod_cast (hshape m n).2.2

def mergedLower (n : ℕ) : ℤ := max (lower 0 n) (lower 1 n)
def mergedUpper (n : ℕ) : ℤ := min (upper 0 n) (upper 1 n)

lemma merge_values : mergedLower 3 = 1 ∧ mergedLower 6 = 3 ∧ mergedLower 9 = 3 := by
  decide +kernel

/-- The merged lower profile fails superadditivity: 1+3>3. -/
theorem merge_not_compatible :
    ¬Compatible (fun n => (mergedLower n : ℝ)) (fun n => (mergedUpper n : ℝ)) := by
  intro h
  have hh := (h.int_lower_increments 3 6).1
  norm_num only [show 3 + 6 = (9 : ℕ) by rfl, merge_values.1,
    merge_values.2.1, merge_values.2.2] at hh

private lemma table_half_bounds : ∀ (i : Fin 2) (n : Fin 12),
    (loTable i)[n.val]! ≤ (n.val / 2 : ℕ) ∧
    ((n.val + 1) / 2 : ℕ) ≤ (hiTable i)[n.val]! := by decide +kernel

lemma half_bounds (i : Fin 2) (n : ℕ) :
    lower i n ≤ (n / 2 : ℕ) ∧ ((n + 1) / 2 : ℕ) ≤ upper i n := by
  have hh := table_half_bounds i ⟨n % 12, Nat.mod_lt _ (by omega)⟩
  have hn : n / 2 = n / 12 * 6 + (n % 12) / 2 := by omega
  have hn' : (n + 1) / 2 = n / 12 * 6 + (n % 12 + 1) / 2 := by omega
  constructor
  · rw [hn]
    simp only [lower, extend, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    linarith [hh.1]
  · rw [hn']
    simp only [upper, extend, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    linarith [hh.2]

/-- An alternating word satisfies the merged bounds, so the failure above is
not caused by inconsistent or empty constraints. -/
theorem common_word_exists : ∃ w : ℤ → Bool,
    SatisfiesIntWindows mergedLower mergedUpper w := by
  let f : ℤ → ℤ := fun a => a / 2
  have hstep (a : ℤ) : 0 ≤ f (a + 1) - f a ∧ f (a + 1) - f a ≤ 1 := by
    dsimp [f]
    omega
  refine ⟨intStepWord f, ?_⟩
  intro a n
  rw [intWordCount_intStepWord f hstep]
  have hc : (n / 2 : ℕ) ≤ f (a + n) - f a ∧
      f (a + n) - f a ≤ ((n + 1) / 2 : ℕ) := by
    dsimp [f]
    omega
  constructor
  · exact (max_le (half_bounds 0 n).1 (half_bounds 1 n).1).trans hc.1
  · exact hc.2.trans (le_min (half_bounds 0 n).2 (half_bounds 1 n).2)

lemma intWordCount_add (w : ℤ → Bool) (a : ℤ) (m n : ℕ) :
    intWordCount w a (m + n) = intWordCount w a m + intWordCount w (a + m) n := by
  simp only [intWordCount, Finset.sum_range_add, Nat.cast_add, add_assoc]

/-- Closing the merged pair really adds information: every satisfying word has
at least4 ones in length9, although the merged lower value there is only3. -/
theorem improved_nine_count (w : ℤ → Bool)
    (hw : SatisfiesIntWindows mergedLower mergedUpper w) :
    4 ≤ intWordCount w 0 9 := by
  have h3 := (hw 0 3).1
  have h6 := (hw 3 6).1
  rw [merge_values.1] at h3
  rw [merge_values.2.1] at h6
  have hadd := intWordCount_add w 0 3 6
  norm_num only [Nat.reduceAdd, Int.reduceAdd, Nat.cast_ofNat] at hadd
  omega

#print axioms merge_not_compatible
#print axioms common_word_exists
#print axioms improved_nine_count
end Erdos970.IntervalRescaling.IntegerHull.MergeExample
