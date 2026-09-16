import Submission.Tree
import Submission.Data94

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_94_valid : check_list 940000 950000 chunk_data_94 = true := by decide
