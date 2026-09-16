import Submission.Tree
import Submission.Data85

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_85_valid : check_list 850000 860000 chunk_data_85 = true := by decide
