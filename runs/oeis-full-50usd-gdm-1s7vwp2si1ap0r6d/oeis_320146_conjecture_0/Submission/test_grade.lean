import Submission.Spec
import Submission.Spec_test

#check (oeis_320146_conjecture_0 : ∃ L : ℝ, Filter.Tendsto
    (fun n : ℕ =>
      (Finset.sum (Finset.Icc 2 n) (fun i => (A320146 i : ℝ)))
      /
      (Finset.sum (Finset.Icc 2 n) (fun i => (prime_oeis i : ℝ))))
    Filter.atTop
    (nhds L))
