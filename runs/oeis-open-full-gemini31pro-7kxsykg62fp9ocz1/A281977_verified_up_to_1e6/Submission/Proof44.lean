import Submission.Tree
import Submission.Data44

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_44_valid : check_list 440000 450000 chunk_data_44 = true := by decide
