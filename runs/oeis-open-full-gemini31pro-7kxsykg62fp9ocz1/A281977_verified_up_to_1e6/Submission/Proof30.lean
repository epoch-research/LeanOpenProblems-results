import Submission.Tree
import Submission.Data30

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_30_valid : check_list 300000 310000 chunk_data_30 = true := by decide
