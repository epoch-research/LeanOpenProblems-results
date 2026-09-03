import Submission.CompletelyMonotoneDifferences
import Submission.HugeFareyDenominatorBound

/-!
The full original scaled tail is not completely monotone. This does not
settle the irrationality conjecture; it blocks a direct transfer of the
columnwise difference argument.
-/

namespace OriginalTailDifferences

open CompletelyMonotoneDifferences Erdos68Development
open scoped fwdDiff

lemma diff_eq_signed_forward (N : ℕ) (f : ℕ → ℝ) (n : ℕ) :
    diff N f n = (-1 : ℝ)^N * (fwdDiff 1)^[N] f n := by
  induction N generalizing n with
  | zero => simp
  | succ N ih =>
    rw [diff_succ, ih, ih, Function.iterate_succ_apply', fwdDiff, pow_succ]
    ring

noncomputable def trialTail (x : ℝ) (n : ℕ) : ℝ :=
  ((n + 1).factorial : ℝ) * (x - ∑ k ∈ Finset.range n, term k)

noncomputable def originalTail (n : ℕ) : ℝ :=
  trialTail (∑' k, term k) n

private def coeff : ℤ := 109499087816928489496181139030903384
private def boundary : ℚ := 20817068081874750788477673876195905695808608693756242069252742226569399703921899340433505632831379597910415448828432172660828403999351928210320283295978824822900931479917241691476825651429045145047165749558359891149482740136345173454184053350125352342493896714903654200649932566713292478181340388535441305161608353446684163308946754350074777622999117763376826717681210906339713829014277736681852921415303047044843600459941417852685764169424425509499849762849029078021880384588602167493142556365645208313336 / 151664924790393919024681326258027801861040534579122446619216967310746772908111368765600601074534693170363473703764931764529239340697996525232191480368736272663916591551734676538662360263016197608538994750249908517294245085156991991365434554053297792307611296683978301604175898983279316701003686205515484623310027929957678960008920364605728855283462034056854565187671551767193369666576539129498580948205188407033522829680700286810966100296097145915107283460960907744040845

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma order_twenty_eight (x : ℝ) :
    diff 28 (trialTail x) 3 = (coeff : ℝ) * x - (boundary : ℝ) := by
  rw [diff_eq_signed_forward, fwdDiff_iter_eq_sum_shift]
  norm_num [trialTail, coeff, boundary, Finset.sum_range_succ, term,
    Nat.factorial, Nat.choose, Nat.reduceAdd]
  ring

private def upper : ℚ :=
  125349875569995347164336093790579894036923220833202 / 10^50

lemma alpha_lt_upper : (∑' k, term k) < (upper : ℝ) := by
  refine (sum_huge_farey_bounds.2).trans ?_
  norm_num [upper]

set_option maxHeartbeats 0 in
lemma negative_difference : diff 28 originalTail 3 < 0 := by
  change diff 28 (trialTail (∑' k, term k)) 3 < 0
  rw [order_twenty_eight]
  have hc : (0 : ℝ) < coeff := by norm_num [coeff]
  have h := mul_lt_mul_of_pos_left alpha_lt_upper hc
  have hn : (coeff : ℝ) * (upper : ℝ) - (boundary : ℝ) < 0 := by
    norm_num [coeff, upper, boundary]
  linarith

theorem originalTail_not_completely_monotone : ¬ CM originalTail := by
  intro h
  exact (not_lt_of_ge (h 28 3)) negative_difference

end OriginalTailDifferences

#print axioms OriginalTailDifferences.negative_difference
#print axioms OriginalTailDifferences.originalTail_not_completely_monotone
