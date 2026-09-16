import Submission.Tree
import Submission.Data36

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_36_valid : check_list 360000 370000 chunk_data_36 = true := by decide
