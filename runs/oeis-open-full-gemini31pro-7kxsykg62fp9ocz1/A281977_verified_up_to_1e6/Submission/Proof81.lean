import Submission.Tree
import Submission.Data81

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_81_valid : check_list 810000 820000 chunk_data_81 = true := by decide
