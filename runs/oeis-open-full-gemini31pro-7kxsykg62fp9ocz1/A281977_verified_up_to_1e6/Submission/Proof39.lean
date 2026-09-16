import Submission.Tree
import Submission.Data39

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem chunk_39_valid : check_list 390000 400000 chunk_data_39 = true := by decide
