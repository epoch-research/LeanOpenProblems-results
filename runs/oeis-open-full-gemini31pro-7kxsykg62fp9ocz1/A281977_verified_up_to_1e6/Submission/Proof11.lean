import Submission.Tree
import Submission.Data11

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_11_valid : check_list 110000 120000 chunk_data_11 = true := by decide
