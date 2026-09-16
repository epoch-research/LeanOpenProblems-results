import Submission.Tree
import Submission.Data18

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_18_valid : check_list 180000 190000 chunk_data_18 = true := by decide
