import Submission.Sieve729Check0
import Submission.Sieve729Check1
import Submission.Sieve729Check2
import Submission.Sieve729Check3
import Submission.Sieve729Check4
import Submission.Sieve729Check5
import Submission.Sieve729Check6
import Submission.Sieve729Check7
import Submission.Sieve729Check8
import Submission.Sieve729Check9
import Submission.Sieve729Check10
import Submission.Sieve729Check11
import Submission.Sieve729Application

/-! A kernel-checked sieve barrier giving a universal lower bound on the squared step size. -/
namespace Erdos952Investigation.Sieve729
open BitsetBarrier
set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma all_rows_checked (r : ℕ) (hr : r ≤ 1180) :
    (dilate period (rowNeighbors rows r) &&& bits r) ||| rows r = rows r := by
  by_cases h0 : r < 100
  · have he : 0 + (r - 0) = r := by omega
    simpa only [he] using block_checked_0 ⟨r - 0, by omega⟩
  by_cases h1 : r < 200
  · have he : 100 + (r - 100) = r := by omega
    simpa only [he] using block_checked_1 ⟨r - 100, by omega⟩
  by_cases h2 : r < 300
  · have he : 200 + (r - 200) = r := by omega
    simpa only [he] using block_checked_2 ⟨r - 200, by omega⟩
  by_cases h3 : r < 400
  · have he : 300 + (r - 300) = r := by omega
    simpa only [he] using block_checked_3 ⟨r - 300, by omega⟩
  by_cases h4 : r < 500
  · have he : 400 + (r - 400) = r := by omega
    simpa only [he] using block_checked_4 ⟨r - 400, by omega⟩
  by_cases h5 : r < 600
  · have he : 500 + (r - 500) = r := by omega
    simpa only [he] using block_checked_5 ⟨r - 500, by omega⟩
  by_cases h6 : r < 700
  · have he : 600 + (r - 600) = r := by omega
    simpa only [he] using block_checked_6 ⟨r - 600, by omega⟩
  by_cases h7 : r < 800
  · have he : 700 + (r - 700) = r := by omega
    simpa only [he] using block_checked_7 ⟨r - 700, by omega⟩
  by_cases h8 : r < 900
  · have he : 800 + (r - 800) = r := by omega
    simpa only [he] using block_checked_8 ⟨r - 800, by omega⟩
  by_cases h9 : r < 1000
  · have he : 900 + (r - 900) = r := by omega
    simpa only [he] using block_checked_9 ⟨r - 900, by omega⟩
  by_cases h10 : r < 1100
  · have he : 1000 + (r - 1000) = r := by omega
    simpa only [he] using block_checked_10 ⟨r - 1000, by omega⟩
  have he : 1100 + (r - 1100) = r := by omega
  simpa only [he] using block_checked_11 ⟨r - 1100, by omega⟩

def certifiedBarrier : PeriodicBarrier.Barrier Allowed :=
  bitset_barrier period 1180 (by decide) (by decide) bits rows
    (fun _ hr => rows_zero hr) (fun r _ c hc => allowed_bits r c hc)
    start_checked all_rows_checked

theorem step_bound_gt_eight (x : ℕ → GaussianInt) (C : ℤ)
    (hx : Function.Injective x)
    (h : ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C) : 8 < C :=
  step_bound_gt_eight_of_barrier certifiedBarrier x C hx h

#print axioms certifiedBarrier
#print axioms step_bound_gt_eight

end Erdos952Investigation.Sieve729
