import Submission.QuarterLaplaceModel

/-! Global rounding bounds for the five-prime count. These require only
32 divisor terms, not enumeration of all starts in the period. -/
namespace Erdos970.GapAverages.QuarterExample
open Finset
set_option maxHeartbeats 2000000

def divCount (m a d : ℕ) : ℤ := ((a+m)/d : ℕ)-(a/d : ℕ)

def ceilCount (m d : ℕ) : ℕ := m/d + if m % d = 0 then 0 else 1

lemma divCount_bounds (m a d : ℕ) (hd : 0 < d) :
    (m/d : ℕ) ≤ divCount m a d ∧ divCount m a d ≤ (ceilCount m d : ℤ) := by
  by_cases hz : m % d = 0
  · have hc : ¬d ≤ a % d + m % d := by
      rw [hz, Nat.add_zero]
      exact not_le_of_gt (Nat.mod_lt a hd)
    have hc' : ¬d ≤ a % d := not_le_of_gt (Nat.mod_lt a hd)
    simp [divCount, Nat.add_div hd, hc', ceilCount, hz]
  · simp only [divCount, Nat.add_div hd, ceilCount, hz, if_false]
    split_ifs <;> push_cast <;> omega

lemma sum_divCount (L : List ℕ) (m a : ℕ) :
    (L.map (divCount m a)).sum =
      (L.map (fun d => ((a+m)/d : ℕ) : ℕ → ℤ)).sum -
        (L.map (fun d => (a/d : ℕ) : ℕ → ℤ)).sum := by
  induction L with
  | nil => simp
  | cons d L ih => simp only [List.map_cons, List.sum_cons, ih, divCount]; ring

def upperCount (m : ℕ) : ℤ :=
  (positiveDivisors.map (fun d => (ceilCount m d : ℤ))).sum -
    (negativeDivisors.map (fun d => ((m/d : ℕ) : ℤ))).sum

lemma prefix_diff_le (m a : ℕ) : fastPrefix (a+m)-fastPrefix a ≤ upperCount m := by
  have hpos : ∀ d ∈ positiveDivisors, 0 < d := by decide
  have hneg : ∀ d ∈ negativeDivisors, 0 < d := by decide
  have hp := List.sum_le_sum (l := positiveDivisors)
    (f := divCount m a) (g := fun d => (ceilCount m d : ℤ))
    (fun d hd => (divCount_bounds m a d (hpos d hd)).2)
  have hn := List.sum_le_sum (l := negativeDivisors)
    (f := fun d => ((m/d : ℕ) : ℤ)) (g := divCount m a)
    (fun d hd => (divCount_bounds m a d (hneg d hd)).1)
  have hh := sub_le_sub hp hn
  rw [sum_divCount, sum_divCount] at hh
  dsimp only [upperCount, fastPrefix]
  simp only [KernelArithmetic.quotient_eq_div]
  convert hh using 1 <;> ring

lemma fastCount_le_upper (m a B : ℕ) (hB : upperCount m ≤ (B : ℤ)) : fastCount m a ≤ B := by
  rw [fastCount, Int.toNat_le]
  exact (prefix_diff_le m a).trans hB

lemma upper_values : upperCount 25236 = 11887 ∧ upperCount 50472 = 23774 := by
  decide +kernel

lemma count_bounds (a : ℕ) : fastCount 25236 a ≤ 11887 ∧ fastCount 50472 a ≤ 23774 := by
  constructor
  · exact fastCount_le_upper 25236 a 11887 upper_values.1.le
  · exact fastCount_le_upper 50472 a 23774 upper_values.2.le

#print axioms count_bounds
end Erdos970.GapAverages.QuarterExample
