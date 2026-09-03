import Submission.Sieve729DataBlock0
import Submission.Sieve729DataBlock1
import Submission.Sieve729DataBlock2
import Submission.Sieve729DataBlock3
import Submission.Sieve729DataBlock4
import Submission.Sieve729DataBlock5
import Submission.Sieve729DataBlock6
import Submission.Sieve729DataBlock7
import Submission.Sieve729DataBlock8
import Submission.Sieve729DataBlock9
import Submission.Sieve729DataBlock10
import Submission.Sieve729DataBlock11

/-! Assembly of the row data; correctness is proved in the separate certificate files. -/
namespace Erdos952Investigation.Sieve729
set_option maxHeartbeats 0

def rows (r : ℕ) : ℕ :=
  if r < 100 then rowList0.getD (r - 0) 0 else
  if r < 200 then rowList1.getD (r - 100) 0 else
  if r < 300 then rowList2.getD (r - 200) 0 else
  if r < 400 then rowList3.getD (r - 300) 0 else
  if r < 500 then rowList4.getD (r - 400) 0 else
  if r < 600 then rowList5.getD (r - 500) 0 else
  if r < 700 then rowList6.getD (r - 600) 0 else
  if r < 800 then rowList7.getD (r - 700) 0 else
  if r < 900 then rowList8.getD (r - 800) 0 else
  if r < 1000 then rowList9.getD (r - 900) 0 else
  if r < 1100 then rowList10.getD (r - 1000) 0 else
  if r < 1180 then rowList11.getD (r - 1100) 0 else
  0

lemma rows_zero {r : ℕ} (hr : 1180 ≤ r) : rows r = 0 := by
  unfold rows
  rw [if_neg (show ¬r < 100 by omega),
    if_neg (show ¬r < 200 by omega),
    if_neg (show ¬r < 300 by omega),
    if_neg (show ¬r < 400 by omega),
    if_neg (show ¬r < 500 by omega),
    if_neg (show ¬r < 600 by omega),
    if_neg (show ¬r < 700 by omega),
    if_neg (show ¬r < 800 by omega),
    if_neg (show ¬r < 900 by omega),
    if_neg (show ¬r < 1000 by omega),
    if_neg (show ¬r < 1100 by omega),
    if_neg (show ¬r < 1180 by omega)]

end Erdos952Investigation.Sieve729
