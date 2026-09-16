import Submission.Tree
import Submission.Data62

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_62_valid : check_list 620000 630000 chunk_data_62 = true := by decide
