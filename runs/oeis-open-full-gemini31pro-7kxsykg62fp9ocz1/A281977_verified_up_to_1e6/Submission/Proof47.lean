import Submission.Tree
import Submission.Data47

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_47_valid : check_list 470000 480000 chunk_data_47 = true := by decide
