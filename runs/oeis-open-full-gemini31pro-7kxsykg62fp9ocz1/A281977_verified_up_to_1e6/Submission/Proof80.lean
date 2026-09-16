import Submission.Tree
import Submission.Data80

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_80_valid : check_list 800000 810000 chunk_data_80 = true := by decide
