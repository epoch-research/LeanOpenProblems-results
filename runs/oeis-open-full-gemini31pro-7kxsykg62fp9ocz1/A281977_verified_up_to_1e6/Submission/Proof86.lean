import Submission.Tree
import Submission.Data86

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_86_valid : check_list 860000 870000 chunk_data_86 = true := by decide
