import Submission.Tree
import Submission.Data99

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_99_valid : check_list 990000 1000001 chunk_data_99 = true := by decide
