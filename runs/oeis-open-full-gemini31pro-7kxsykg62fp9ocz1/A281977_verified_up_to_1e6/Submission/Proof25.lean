import Submission.Tree
import Submission.Data25

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_25_valid : check_list 250000 260000 chunk_data_25 = true := by decide
