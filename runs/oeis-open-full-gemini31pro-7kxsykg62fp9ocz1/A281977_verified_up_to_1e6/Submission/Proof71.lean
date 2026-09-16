import Submission.Tree
import Submission.Data71

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_71_valid : check_list 710000 720000 chunk_data_71 = true := by decide
