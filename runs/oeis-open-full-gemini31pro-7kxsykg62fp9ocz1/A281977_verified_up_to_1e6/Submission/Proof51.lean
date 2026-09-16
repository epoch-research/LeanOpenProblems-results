import Submission.Tree
import Submission.Data51

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_51_valid : check_list 510000 520000 chunk_data_51 = true := by decide
