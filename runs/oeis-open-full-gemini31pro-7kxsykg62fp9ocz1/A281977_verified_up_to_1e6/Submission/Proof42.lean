import Submission.Tree
import Submission.Data42

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_42_valid : check_list 420000 430000 chunk_data_42 = true := by decide
