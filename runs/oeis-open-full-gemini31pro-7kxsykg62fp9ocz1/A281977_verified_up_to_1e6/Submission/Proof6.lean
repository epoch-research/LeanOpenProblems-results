import Submission.Tree
import Submission.Data6

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_6_valid : check_list 60000 70000 chunk_data_6 = true := by decide
