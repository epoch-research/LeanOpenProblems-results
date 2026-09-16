import Submission.Tree
import Submission.Data8

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_8_valid : check_list 80000 90000 chunk_data_8 = true := by decide
