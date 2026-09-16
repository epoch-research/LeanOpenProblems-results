import Submission.Tree
import Submission.Data65

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_65_valid : check_list 650000 660000 chunk_data_65 = true := by decide
