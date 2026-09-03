import Submission.WindowClosureRealization
import Submission.WindowClosurePeriodic

/-! Truncated translated-window constraints can be strictly weaker than the
complete periodic profile, even after adding a consistent block lower bound.
This example concerns binary words, not prime residues. -/
namespace Erdos970.WindowConstraintClosure.TruncationExample
open IntervalRescaling.IntegerHull

def distance (z : ℤ) : ℤ := 6 * (z / 12) + min (z % 12) 6

lemma distance_isDistance : IsDistance distance := by
  constructor
  · decide
  · intro x y
    simp only [distance]
    omega

lemma distance_periodic (z : ℤ) : distance (z + 12) = distance z + 6 := by
  simp only [distance]
  omega

lemma distance_unit : distance (-1) ≤ 0 ∧ distance 1 ≤ 1 := by decide

/-- The exact closure forces at most two ones in a window of length three. -/
theorem closed_three : addLower distance 4 2 3 = 2 := by
  have hh := periodic_addLower_eq_finset_min (Q := 12) (R := 6) (g := 4) (b := 2)
    distance_isDistance (by decide) distance_periodic (by decide) 3
  convert hh using 1


/-- A denser word passes all length-at-most-seven original tests, as well as the
new lower bound on every length-four window. -/
def truncatedWord (a : ℤ) : Bool := decide (a % 4 < 3)

lemma truncatedWord_count_mod (a : ℤ) (n : ℕ) :
    intWordCount truncatedWord a n = intWordCount truncatedWord (a % 4) n := by
  simp only [intWordCount]
  apply Finset.sum_congr rfl
  intro i hi
  have he : truncatedWord (a + i) = truncatedWord (a % 4 + i) := by
    simp [truncatedWord, Int.add_emod]
  rw [he]

lemma finite_checks :
    (∀ a : Fin 4, ∀ n : Fin 8,
      -distance (-((n.val : ℕ) : ℤ)) ≤ (intWordCount truncatedWord a.val n.val : ℤ) ∧
      (intWordCount truncatedWord a.val n.val : ℤ) ≤ distance n.val) ∧
    (∀ a : Fin 4, intWordCount truncatedWord a.val 4 = 3) ∧
    intWordCount truncatedWord 0 3 = 3 := by
  decide +kernel

lemma truncatedWord_windows (a : ℤ) (n : ℕ) (hn : n ≤ 7) :
    -distance (-(n : ℤ)) ≤ (intWordCount truncatedWord a n : ℤ) ∧
      (intWordCount truncatedWord a n : ℤ) ≤ distance n := by
  rw [truncatedWord_count_mod]
  let a' : Fin 4 := ⟨(a % 4).toNat, by omega⟩
  have he : (a'.val : ℤ) = a % 4 := by simp only [a']; omega
  have hh := finite_checks.1 a' ⟨n, by omega⟩
  simpa only [he] using hh

lemma truncatedWord_lowerBlock : LowerBlock (wordCumulative truncatedWord) 4 2 := by
  intro a
  have hcount : intWordCount truncatedWord a 4 = 3 := by
    rw [truncatedWord_count_mod]
    let a' : Fin 4 := ⟨(a % 4).toNat, by omega⟩
    have he : (a'.val : ℤ) = a % 4 := by simp only [a']; omega
    simpa only [he] using finite_checks.2.1 a'
  have hh := wordCumulative_count truncatedWord a 4
  rw [hcount] at hh
  change 2 ≤ wordCumulative truncatedWord (a + (4 : ℕ)) - wordCumulative truncatedWord a
  omega

/-- Thus the exact upper improvement cannot follow just from all translated old
windows of lengths at most seven and the new lower block constraint. -/
theorem finite_window_information_insufficient :
    ¬(∀ w : ℤ → Bool,
      (∀ (a : ℤ) (n : ℕ), n ≤ 7 →
        -distance (-(n : ℤ)) ≤ (intWordCount w a n : ℤ) ∧
        (intWordCount w a n : ℤ) ≤ distance n) →
      LowerBlock (wordCumulative w) 4 2 → intWordCount w 0 3 ≤ 2) := by
  intro h
  have hh := h truncatedWord truncatedWord_windows truncatedWord_lowerBlock
  rw [finite_checks.2.2] at hh
  omega

/-- With the full original profile, the improvement is valid for every model. -/
theorem full_window_information_sufficient :
    ∀ w : ℤ → Bool, WordModel distance 4 2 w → intWordCount w 0 3 ≤ 2 := by
  have hF := balanced_admissible distance_isDistance (Q := 12) (R := 6)
    (by decide) distance_periodic
  have hB := balanced_lowerBlock (Q := 12) (R := 6) (g := 4) (b := 2)
    (by decide) (by decide)
  have hh := (window_upper_iff distance_isDistance distance_unit.1 distance_unit.2
    hF hB 3 2).mpr closed_three.le
  intro w hw
  exact_mod_cast hh w hw

#print axioms finite_window_information_insufficient
#print axioms full_window_information_sufficient
end Erdos970.WindowConstraintClosure.TruncationExample
