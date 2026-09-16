import Submission.Tree
import Submission.Data79

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_79_valid : check_list 790000 800000 chunk_data_79 = true := by decide
