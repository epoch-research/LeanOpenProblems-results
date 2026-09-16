import Submission.Tree
import Submission.Data40

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_40_valid : check_list 400000 410000 chunk_data_40 = true := by decide
