import Submission.TriangleOutsideCheck1
import Submission.TriangleOutsideCheck2
import Submission.TriangleOutsideCheck3
import Submission.TriangleOutsideRejections

/-! Soundness of the finite normalized triangle-outside classification. -/
namespace Erdos184.TriangleOutsideData
open SmallGraphEncoding CyclePairCertificate
set_option maxHeartbeats 1000000

lemma rejection_sound (r : Rejection) (hr : checkRejection r = true) :
    ¬ EvenCycleCore.NoTwoCycles (graph 6 r.degree r.code) := by
  simp only [checkRejection, decide_eq_true_eq] at hr
  intro hG
  exact contradict_no_two hG r.first.vertex r.second.vertex
    hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2

lemma rejector_sound (d code : ℕ) (hG : EvenCycleCore.NoTwoCycles (graph 6 d code)) :
    rejector d code = none := by
  cases he : rejector d code with
  | none => rfl
  | some r =>
    have hm := List.mem_of_find?_eq_some he
    have hp := List.find?_some he
    simp only [decide_eq_true_eq] at hp
    have hc := rejections_checked
    rw [← Array.all_toList, List.all_eq_true] at hc
    have hr := hc r hm
    apply False.elim
    apply rejection_sound r hr
    simpa only [hp.1,hp.2] using hG

lemma range_checked (d n : ℕ) (hd : 1 ≤ d) (hd' : d ≤ 3)
    (hn : 2 ≤ n) (hn' : n ≤ 6) : checkRange d n 10 0 = true := by
  interval_cases d <;> interval_cases n
  · exact range_checked_1_2
  · exact range_checked_1_3
  · exact range_checked_1_4
  · exact range_checked_1_5
  · exact range_checked_1_6
  · exact range_checked_2_2
  · exact range_checked_2_3
  · exact range_checked_2_4
  · exact range_checked_2_5
  · exact range_checked_2_6
  · exact range_checked_3_2
  · exact range_checked_3_3
  · exact range_checked_3_4
  · exact range_checked_3_5
  · exact range_checked_3_6

lemma classification (d n code : ℕ) (hd : 1 ≤ d) (hd' : d ≤ 3)
    (hn : 2 ≤ n) (hn' : n ≤ 6) (hcode : code < 1024)
    (he : eligible d n code = true)
    (hG : EvenCycleCore.NoTwoCycles (graph 6 d code)) : good d n code = true := by
  have hh := checkRange_sound d n 10 0 (range_checked d n hd hd' hn hn')
    code (by norm_num; exact hcode)
  simpa only [Nat.zero_add,classified,he,rejector_sound d code hG,
    Bool.not_true,Bool.false_or,Option.isSome_none,Bool.or_false] using hh

end Erdos184.TriangleOutsideData
